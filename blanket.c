#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/wait.h>

typedef enum {
    EXPR_NUMBER,
    EXPR_IDENT,
    EXPR_ADD,
    EXPR_SUB,
    EXPR_MUL,
    EXPR_DIV,
    EXPR_MOD,
} ExpressionKind;

typedef struct Expression {
    ExpressionKind kind;

    union {
        long number;
        char *ident;
        struct {
            struct Expression *left;
            struct Expression *right;
        } binop;
    } as;
} Expression;

typedef enum {
    COND_LT,
    COND_LTE,
    COND_GT,
    COND_GTE,
    COND_EQ,
    COND_NEQ
} ConditionKind;

typedef struct {
    ConditionKind kind;

    Expression *left;
    Expression *right;
} Condition;

typedef struct {
    char *name;
    Expression *expression;
} Declaration;

typedef struct {
    char *name;
    Expression *expression;
} Assignment;

typedef struct {
    char *name;
    Expression **arguments;
    size_t argument_count;
} FunctionCall;

typedef struct {
    char *name;
} External;

typedef struct IfStatement IfStatement;
typedef struct WhileStatement WhileStatement;
typedef struct Statement Statement;

typedef enum {
    DECLARATION,
    ASSIGNMENT,
    FUNCTION_CALL,
    EXTERNAL,
    IF_STATEMENT,
    WHILE_STATEMENT,
} StatementKind;

typedef struct Statement {
    union {
        Declaration *declaration;
        Assignment *assignment;
        FunctionCall *function_call;
        External *external;
        IfStatement *if_statement;
        WhileStatement *while_statement;
    } as;
    StatementKind kind;
} Statement;

typedef struct IfStatement {
    Condition *condition;
    Statement **statements;
    size_t statement_count;
} IfStatement;

typedef struct WhileStatement {
    Condition *condition;
    Statement **statements;
    size_t statement_count;
} WhileStatement;

typedef struct {
    char *base;
    char *head;
    char **symbols;
    size_t symbol_count;
    int label_count;
} Emitter;

void p(Emitter *e, const char *fmt, ...) {
    char buf[128];
    va_list a;
    va_start(a, fmt);
    size_t n = vsnprintf(buf, sizeof(buf), fmt, a);
    va_end(a);
    memcpy(e->head, buf, n);
    e->head[n] = '\n';
    e->head += n + 1;
}

char *new_label(Emitter *e) {
    char *label = malloc(sizeof(char) * 10);
    snprintf(label, 10, "_L%d", e->label_count++);
    return label;
}

int get_symbol(Emitter *e, const char *symbol) {
    size_t i = 0;
    while (i < e->symbol_count) {
        if (strcmp(symbol, e->symbols[i]) == 0) break;
        i++;
    }
    if (i >= e->symbol_count) {
        return -1;
    }
    return (i + 1) * 8;
}

void push_symbol(Emitter *e, char *symbol) {
    if (get_symbol(e, symbol) >= 0) {
        fprintf(stderr, "Symbol %s already declared\n", symbol);
        exit(1);
    }
    e->symbols[e->symbol_count++] = symbol;
}

void emit_expression(Emitter *e, Expression *expression) {
    switch (expression->kind) {
        case EXPR_NUMBER:
            p(e, "push %ld", expression->as.number);
            break;
        case EXPR_IDENT:
            {
                int symbol_offset = get_symbol(e, expression->as.ident);
                if (symbol_offset < 0) {
                    fprintf(stderr, "Undeclared symbol %s\n", expression->as.ident);
                    exit(1);
                }
                p(e, "push [rbp-%d]", get_symbol(e, expression->as.ident));
                break;
            }
        case EXPR_ADD:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "add rax, rbx");
            p(e, "push rax");
            break;
        case EXPR_SUB:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "sub rax, rbx");
            p(e, "push rax");
            break;
        case EXPR_MUL:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "imul rbx");
            p(e, "push rax");
            break;
        case EXPR_DIV:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cqo");
            p(e, "idiv rbx");
            p(e, "push rax");
            break;
        case EXPR_MOD:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cqo");
            p(e, "idiv rbx");
            p(e, "push rdx");
            break;
    }
}

void emit_condition(Emitter *e, Condition *condition) {
    emit_expression(e, condition->left);
    emit_expression(e, condition->right);
    p(e, "pop rbx");
    p(e, "pop rax");
    p(e, "cmp rax, rbx");
    switch (condition->kind) {
        case COND_LT:
            p(e, "setl al");
            break;
        case COND_LTE:
            p(e, "setle al");
            break;
        case COND_GT:
            p(e, "setg al");
            break;
        case COND_GTE:
            p(e, "setge al");
            break;
        case COND_EQ:
            p(e, "sete al");
            break;
        case COND_NEQ:
            p(e, "setne al");
            break;
        default:
            fprintf(stderr, "Unknown condition kind %d\n", condition->kind);
            exit(1);
    }
}

void emit_declaration(Emitter *e, Declaration *declaration) {
    p(e, "sub rsp, 8");

    push_symbol(e, declaration->name);
    emit_expression(e, declaration->expression);

    p(e, "pop rax");
    p(e, "mov [rsp], rax");
}

void emit_assignment(Emitter *e, Assignment *assignment) {
    emit_expression(e, assignment->expression);
    p(e, "pop rax");

    int symbol_offset = get_symbol(e, assignment->name);
    if (symbol_offset < 0) {
        fprintf(stderr, "Undeclared symbol %s\n", assignment->name);
        exit(1);
    }

    p(e, "mov [rbp-%d], rax", symbol_offset);
}

void emit_function_call(Emitter *e, FunctionCall *function_call) {
    const char *call_registers[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};

    for (size_t i = 0; i < function_call->argument_count; i++) {
        emit_expression(e, function_call->arguments[i]);
        p(e, "pop %s", call_registers[i]);
    }

    p(e, "call %s", function_call->name);
}

void emit_external(Emitter *e, External *external) {
    p(e, "extrn %s", external->name);
}

void emit_statements(Emitter *e, Statement **statements, size_t statement_count);

void emit_if_statement(Emitter *e, IfStatement *if_statement) {
    char *label = new_label(e);

    emit_condition(e, if_statement->condition);
    p(e, "test al, al");
    p(e, "jz %s", label);

    emit_statements(e, if_statement->statements, if_statement->statement_count);

    p(e, "%s:", label);
}

void emit_while_statement(Emitter *e, WhileStatement *while_statement) {
    char *start_label = new_label(e);
    char *end_label = new_label(e);

    p(e, "%s:", start_label);
    emit_condition(e, while_statement->condition);
    p(e, "test al, al");
    p(e, "jz %s", end_label);

    emit_statements(e, while_statement->statements, while_statement->statement_count);

    p(e, "jmp %s", start_label);
    p(e, "%s:", end_label);
}

void emit_statements(Emitter *e, Statement **statements, size_t statement_count) {
    for (size_t i = 0; i < statement_count; i++) {
        Statement *s = statements[i];

        switch (s->kind) {
            case DECLARATION:
                emit_declaration(e, s->as.declaration);
                break;
            case ASSIGNMENT:
                emit_assignment(e, s->as.assignment);
                break;
            case FUNCTION_CALL:
                emit_function_call(e, s->as.function_call);
                break;
            case EXTERNAL:
                emit_external(e, s->as.external);
                break;
            case IF_STATEMENT:
                emit_if_statement(e, s->as.if_statement);
                break;
            case WHILE_STATEMENT:
                emit_while_statement(e, s->as.while_statement);
                break;
            default:
                fprintf(stderr, "Expected statement but found %d\n", s->kind);
                exit(1);
                break;
        }
    }
}

void emit(Emitter *e, Statement **ast, size_t statement_count) {
    char header[] = "format ELF64\n\
public main\n\
section '.text' executable\n\
main:\n\
push rbp\n\
mov rbp, rsp\n";

    memcpy(e->head, header, sizeof(header)-1);
    e->head += sizeof(header)-1;

    emit_statements(e, ast, statement_count);

    char footer[] = "leave\nret\n";

    memcpy(e->head, footer, sizeof(footer)-1);
    e->head += sizeof(footer)-1;
}

typedef enum {
    T_EOF,
    T_LET,
    T_IDENT,
    T_EQUALS,
    T_INTLIT,
    T_PLUS,
    T_MINUS,
    T_STAR,
    T_SLASH,
    T_PERCENT,
    T_LT,
    T_GT,
    T_LTE,
    T_GTE,
    T_EQ,
    T_NEQ,
    T_SEMICOLON,
    T_NEWLINE,
    T_LPAREN,
    T_RPAREN,
    T_COMMA,
    T_EXTERN,
    T_IF,
    T_WHILE,
    T_LCURLY,
    T_RCURLY,
} TokenKind;

typedef struct {
    TokenKind kind;
    union {
        long l;
        char *s;
    } value;
} Token;

typedef struct {
    Token *cursor;
    Token *end;
} Parser;

Token peek(Parser *p) {
    if (p->cursor >= p->end) return (Token){T_EOF, {0}};
    return *p->cursor;
}

Token peekn(Parser *p, int n) {
    if (p->cursor+n >= p->end) return (Token){T_EOF, {0}};
    return p->cursor[n];
}

Token next(Parser *p) {
    Token t = peek(p);
    p->cursor++;
    return t;
}

Token require(Parser *p, TokenKind token_kind) {
    Token t = next(p);
    if (t.kind != token_kind) {
        fprintf(stderr, "Expected token kind %d, found %d\n", token_kind, t.kind);
        exit(1);
    }
    return t;
}

Expression *parse_factor(Parser *p) {
    Expression *expr = malloc(sizeof(Expression));

    Token t = next(p);
    switch (t.kind) {
        case T_INTLIT:
            expr->kind = EXPR_NUMBER;
            expr->as.number = t.value.l;
            break;
        case T_IDENT:
            expr->kind = EXPR_IDENT;
            expr->as.ident = t.value.s;
            break;
        default:
            fprintf(stderr, "Unexpected token in factor\n");
            exit(1);
    }

    return expr;
}

Expression *parse_term(Parser *p) {
    Expression *left = parse_factor(p);

    while (peek(p).kind == T_STAR || peek(p).kind == T_SLASH || peek(p).kind == T_PERCENT) {
        Token t = next(p);

        Expression *right = parse_factor(p);

        Expression *op = malloc(sizeof(Expression));

        op->kind = t.kind == T_STAR ? EXPR_MUL : t.kind == T_SLASH ? EXPR_DIV : EXPR_MOD;
        op->as.binop.left = left;
        op->as.binop.right = right;

        left = op;
    }

    return left;
}

Expression *parse_expression(Parser *p) {
    Expression *left = parse_term(p);

    while (peek(p).kind == T_PLUS || peek(p).kind == T_MINUS) {
        Token t = next(p);

        Expression *right = parse_term(p);

        Expression *op = malloc(sizeof(Expression));

        op->kind = t.kind == T_PLUS ? EXPR_ADD : EXPR_SUB;
        op->as.binop.left = left;
        op->as.binop.right = right;

        left = op;
    }

    return left;
}

Condition *parse_condition(Parser *p) {

    Condition *cond = malloc(sizeof(Condition));

    cond->left = parse_expression(p);

    Token t = next(p);
    switch (t.kind) {
        case T_LT:
            cond->kind = COND_LT;
            break;
        case T_LTE:
            cond->kind = COND_LTE;
            break;
        case T_GT:
            cond->kind = COND_GT;
            break;
        case T_GTE:
            cond->kind = COND_GTE;
            break;
        case T_EQ:
            cond->kind = COND_EQ;
            break;
        case T_NEQ:
            cond->kind = COND_NEQ;
            break;
        default:
            fprintf(stderr, "Expected condition to have one of <, <=, >, >=, ==, or != but found %d\n", t.kind);
            exit(1);
    }

    cond->right = parse_expression(p);

    return cond;
}

Declaration *parse_declaration(Parser *p) {
    Declaration *decl = malloc(sizeof(Declaration));

    require(p, T_LET);
    Token name = require(p, T_IDENT);
    require(p, T_EQUALS);
    decl->name = name.value.s;
    decl->expression = parse_expression(p);

    return decl;
}

Assignment *parse_assignment(Parser *p) {
    Assignment *ass = malloc(sizeof(Assignment));

    Token name = require(p, T_IDENT);
    require(p, T_EQUALS);
    ass->name = name.value.s;
    ass->expression = parse_expression(p);

    return ass;
}

FunctionCall *parse_function_call(Parser *p) {
    FunctionCall *call = malloc(sizeof(FunctionCall));

    Token name = require(p, T_IDENT);
    call->name = name.value.s;

    require(p, T_LPAREN);

    call->arguments = malloc(sizeof(Expression*) * 8);

    size_t arg_count = 0;
    while (peek(p).kind != T_RPAREN) {
        call->arguments[arg_count] = parse_expression(p);
        arg_count++;
        if (peek(p).kind != T_RPAREN) require(p, T_COMMA);
    }

    call->argument_count = arg_count;

    require(p, T_RPAREN);

    return call;
}

size_t parse(Parser *p, Statement **program);

IfStatement *parse_if_statement(Parser *p) {
    IfStatement *ifs = malloc(sizeof(IfStatement));

    require(p, T_IF);
    ifs->condition = parse_condition(p);
    require(p, T_LCURLY);
    Statement **statements = malloc(sizeof(Statement*) * 100);
    size_t statement_count = parse(p, statements);

    ifs->statements = statements;
    ifs->statement_count = statement_count;

    require(p, T_RCURLY);

    return ifs;
}

WhileStatement *parse_while_statement(Parser *p) {
    WhileStatement *whil = malloc(sizeof(WhileStatement));

    require(p, T_WHILE);
    whil->condition = parse_condition(p);
    require(p, T_LCURLY);
    Statement **statements = malloc(sizeof(Statement*) * 100);
    size_t statement_count = parse(p, statements);

    whil->statements = statements;
    whil->statement_count = statement_count;

    require(p, T_RCURLY);

    return whil;
}

External *parse_external(Parser *p) {
    External *ext = malloc(sizeof(External));

    require(p, T_EXTERN);
    Token name = require(p, T_IDENT);
    ext->name = name.value.s;

    return ext;
}

Statement *parse_statement(Parser *p) {
    Statement *s = malloc(sizeof(Statement));

    for (Token x = peek(p); x.kind == T_NEWLINE || x.kind == T_SEMICOLON; x = peek(p))
        next(p);

    switch (peek(p).kind) {
        case T_LET:
            s->kind = DECLARATION;
            s->as.declaration = parse_declaration(p);
            break;
        case T_IDENT:
            {
                TokenKind second = peekn(p, 1).kind;
                if (second == T_LPAREN) {
                    s->kind = FUNCTION_CALL;
                    s->as.function_call = parse_function_call(p);
                } else if (second == T_EQUALS) {
                    s->kind = ASSIGNMENT;
                    s->as.assignment = parse_assignment(p);
                }
                break;
            }
        case T_EXTERN:
            s->kind = EXTERNAL;
            s->as.external = parse_external(p);
            break;
        case T_IF:
            s->kind = IF_STATEMENT;
            s->as.if_statement = parse_if_statement(p);
            break;
        case T_WHILE:
            s->kind = WHILE_STATEMENT;
            s->as.while_statement = parse_while_statement(p);
            break;
        default:
            fprintf(stderr, "Expected statement but found %d\n", peek(p).kind);
            exit(1);
    }

    for (Token x = peek(p); x.kind == T_NEWLINE || x.kind == T_SEMICOLON; x = peek(p))
        next(p);

    return s;
}

size_t parse(Parser *p, Statement **program) {
    int i = 0;
    while (peek(p).kind != T_EOF && peek(p).kind != T_RCURLY) {
        program[i++] = parse_statement(p);
    }
    return i;
}

typedef struct {
    char *base;
    char *head;
} Lexer;

char l_peek(Lexer *l) {
    return *l->head;
}

char l_next(Lexer *l) {
    char c = l_peek(l);
    if (c != '\0') l->head++;
    return c;
}

Token lex_token(Lexer *l) {
    while (isspace(l_peek(l)) && l_peek(l) != '\n') l_next(l);

    char c = l_next(l);

    if (c == '\n') {
        while (isspace(l_peek(l))) l_next(l);
        return (Token){T_NEWLINE, {0}};
    }
    if (c == '+') return (Token){T_PLUS, {0}};
    if (c == '-') return (Token){T_MINUS, {0}};
    if (c == '*') return (Token){T_STAR, {0}};
    if (c == '/') return (Token){T_SLASH, {0}};
    if (c == '%') return (Token){T_PERCENT, {0}};
    if (c == ';') return (Token){T_SEMICOLON, {0}};
    if (c == '(') return (Token){T_LPAREN, {0}};
    if (c == ')') return (Token){T_RPAREN, {0}};
    if (c == ',') return (Token){T_COMMA, {0}};
    if (c == '{') return (Token){T_LCURLY, {0}};
    if (c == '}') return (Token){T_RCURLY, {0}};
    if (c == '=') {
        if (l_peek(l) == '=') {
            l_next(l);
            return (Token){T_EQ, {0}};
        }
        return (Token){T_EQUALS, {0}};
    }
    if (c == '!') {
        if (l_peek(l) == '=') {
            l_next(l);
            return (Token){T_NEQ, {0}};
        }
    }
    if (c == '<') {
        if (l_peek(l) == '=') {
            l_next(l);
            return (Token){T_LTE, {0}};
        }
        return (Token){T_LT, {0}};
    }
    if (c == '>') {
        if (l_peek(l) == '=') {
            l_next(l);
            return (Token){T_GTE, {0}};
        }
        return (Token){T_GT, {0}};
    }

    if (isdigit(c)) {
        long number = c - '0';
        while (isdigit(l_peek(l))) {
            number *= 10;
            number += l_next(l) - '0';
        }
        if (isalpha(l_peek(l))) {
            fprintf(stderr, "Identifiers must not start with digits\n");
            exit(1);
        }
        return (Token){T_INTLIT, { .l = number }};
    }

    if (!isalnum(c)) {
        fprintf(stderr, "Unexpected character %c at byte %ld\n", c, l->head-l->base);
        exit(1);
    }

    char *token = calloc(1, sizeof(char) * 0x100);

    token[0] = c;

    int i = 1;
    while (isalnum(l_peek(l))) {
        token[i++] = l_next(l);
    }

    if (strcmp(token, "let") == 0) return (Token){T_LET, {0}};
    if (strcmp(token, "extern") == 0) return (Token){T_EXTERN, {0}};
    if (strcmp(token, "if") == 0) return (Token){T_IF, {0}};
    if (strcmp(token, "while") == 0) return (Token){T_WHILE, {0}};

    return (Token){T_IDENT, { .s = token }};
}

size_t lex(Lexer *l, Token *tokens) {
    int i = 0;
    while (l_peek(l) != '\0') {
        tokens[i++] = lex_token(l);
    }

    tokens[i++] = (Token){T_EOF, {0}};

    return i;
}

char *replace_ext(const char *filename, const char *new_extension) {
    const char *dot = strrchr(filename, '.');
    size_t len = dot ? (size_t)(dot - filename) : strlen(filename);

    char *out = malloc(len + strlen(new_extension) + 1);
    memcpy(out, filename, len);
    strcpy(out + len, new_extension);

    return out;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: ./blanket filename\n");
        exit(1);
    }

    char *filename = argv[1];

    FILE *fp = fopen(filename, "r");
    if (fp == NULL) {
        fprintf(stderr, "Could not open file %s\n", filename);
        exit(1);
    }
    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    rewind(fp);

    char *code = malloc(size*sizeof(char));
    fread(code, 1, size, fp);
    fclose(fp);
    
    Token tokens[0x1000];
    Lexer l = {code, code};
    size_t token_count = lex(&l, tokens);

    Statement *program[100];
    Parser p = {tokens, tokens + token_count};
    size_t statement_count = parse(&p, program);

    char assembly[0x100000] = {0};
    char *symbols[0x100];
    Emitter e = {assembly, assembly, symbols, 0, 0};
    emit(&e, program, statement_count);

    char *asm_filename = replace_ext(filename, ".asm");

    FILE *asm_fp = fopen(asm_filename, "w");
    fputs(assembly, asm_fp);
    fclose(asm_fp);

    char *object_filename = replace_ext(filename, ".o");

    int fasm_process = fork();
    if (fasm_process == 0) {
        execlp("fasm2", "fasm2", "-n", asm_filename, object_filename, NULL);
    }
    waitpid(fasm_process, 0, 0);

    char *out_filename = replace_ext(filename, "");

    int clang_process = fork();
    if (clang_process == 0) {
        execlp("clang", "clang", "-no-pie", "-o", out_filename, object_filename, NULL);
    }
    waitpid(clang_process, 0, 0);

    remove(object_filename);
}
