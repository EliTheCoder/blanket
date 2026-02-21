#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>
#include <unistd.h>
#include <sys/wait.h>

const char * const call_registers[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};

typedef enum {
    EXPR_NUMBER,
    EXPR_STRING,
    EXPR_IDENT,
    EXPR_AND,
    EXPR_OR,
    EXPR_ADD,
    EXPR_SUB,
    EXPR_MUL,
    EXPR_DIV,
    EXPR_MOD,
    EXPR_LT,
    EXPR_LTE,
    EXPR_GT,
    EXPR_GTE,
    EXPR_EQ,
    EXPR_NEQ,
    EXPR_FUNCTION_CALL,
} ExpressionKind;

typedef struct FunctionCall FunctionCall;
typedef struct Expression Expression;

typedef struct Expression {
    ExpressionKind kind;

    union {
        long number;
        char *ident;
        char *string;
        FunctionCall *function_call;
        struct {
            struct Expression *left;
            struct Expression *right;
        } binop;
    } as;
} Expression;

typedef struct {
    char *name;
    Expression *expression;
} Declaration;

typedef struct {
    char *name;
    Expression *expression;
} Assignment;

typedef struct FunctionCall {
    char *name;
    Expression **arguments;
    size_t argument_count;
} FunctionCall;

typedef struct {
    char *name;
} External;

typedef struct {
    Expression *expression;
} ReturnStatement;

typedef struct IfStatement IfStatement;
typedef struct WhileStatement WhileStatement;
typedef struct Function Function;
typedef struct Statement Statement;

typedef enum {
    DECLARATION,
    ASSIGNMENT,
    FUNCTION_CALL,
    EXTERNAL,
    IF_STATEMENT,
    WHILE_STATEMENT,
    FUNCTION,
    RETURN_STATEMENT,
} StatementKind;

typedef struct Statement {
    union {
        Declaration *declaration;
        Assignment *assignment;
        FunctionCall *function_call;
        External *external;
        IfStatement *if_statement;
        WhileStatement *while_statement;
        Function *function;
        ReturnStatement *return_statement;
    } as;
    StatementKind kind;
} Statement;

typedef struct Function {
    char *name;
    char **parameters;
    size_t parameter_count;
    Statement **statements;
    size_t statement_count;
} Function;

typedef struct IfStatement {
    Expression *condition;
    Statement **body_statements;
    size_t body_statement_count;
    Statement **else_statements;
    size_t else_statement_count;
} IfStatement;

typedef struct WhileStatement {
    Expression *condition;
    Statement **statements;
    size_t statement_count;
} WhileStatement;

typedef struct {
    char *base;
    char *head;
    char *back_base;
    char *back_head;
    char **symbols;
    size_t symbol_count;
    int label_count;
    char **strings;
    int string_count;
} Emitter;

void pn(Emitter *e, const char *fmt, ...) {
    char buf[128];
    va_list a;
    va_start(a, fmt);
    size_t n = vsnprintf(buf, sizeof(buf), fmt, a);
    va_end(a);
    memcpy(e->head, buf, n);
    e->head += n;
}

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

void p_back(Emitter *e, const char *fmt, ...) {
    char buf[128];
    va_list a;
    va_start(a, fmt);
    size_t n = vsnprintf(buf, sizeof(buf), fmt, a);
    va_end(a);
    memcpy(e->back_head, buf, n);
    e->back_head[n] = '\n';
    e->back_head += n + 1;
}

char *new_label(Emitter *e) {
    char *label = malloc(sizeof(char) * 10);
    snprintf(label, 10, "_L%d", e->label_count++);
    return label;
}

char *push_string(Emitter *e, char *str) {
    char *label = malloc(sizeof(char) * 10);
    snprintf(label, 10, "_LD%d", e->string_count);

    e->strings[e->string_count] = str;

    e->string_count++;
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
    return (i + 1) * 16;
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
        case EXPR_STRING:
            {
                char *str_label = push_string(e, expression->as.string);
                p(e, "push %s", str_label);
                break;
            }
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
        case EXPR_FUNCTION_CALL:
            {
                for (size_t i = 0; i < expression->as.function_call->argument_count; i++) {
                    emit_expression(e, expression->as.function_call->arguments[i]);
                }
                for (int i = expression->as.function_call->argument_count - 1; i >= 0; i--) {
                    p(e, "pop %s", call_registers[i]);
                }

                p(e, "xor rax, rax");
                p(e, "call %s", expression->as.function_call->name);
                p(e, "push rax");
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
        case EXPR_LT:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "setl al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_LTE:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "setle al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_GT:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "setg al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_GTE:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "setge al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_EQ:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "sete al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_NEQ:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "cmp rax, rbx");
            p(e, "setne al");
            p(e, "movzx rax, al");
            p(e, "push rax");
            break;
        case EXPR_AND:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "test rbx, rbx");
            p(e, "cmovz rax, rbx");
            p(e, "push rax");
            break;
        case EXPR_OR:
            emit_expression(e, expression->as.binop.left);
            emit_expression(e, expression->as.binop.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "or rax, rbx");
            p(e, "push rax");
            break;
    }
}

void emit_declaration(Emitter *e, Declaration *declaration) {
    p(e, "sub rsp, 16");

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
    for (size_t i = 0; i < function_call->argument_count; i++) {
        emit_expression(e, function_call->arguments[i]);
    }
    for (int i = function_call->argument_count - 1; i >= 0; i--) {
        p(e, "pop %s", call_registers[i]);
    }

    p(e, "xor rax, rax");
    p(e, "call %s", function_call->name);
}

void emit_external(Emitter *e, External *external) {
    p(e, "extrn %s", external->name);
}

void emit_statements(Emitter *e, Statement **statements, size_t statement_count);

void emit_if_statement(Emitter *e, IfStatement *if_statement) {
    char *end_label = new_label(e);
    char *else_label = new_label(e);

    emit_expression(e, if_statement->condition);
    p(e, "pop rax");
    p(e, "test rax, rax");
    p(e, "jz %s", else_label);

    emit_statements(e, if_statement->body_statements, if_statement->body_statement_count);

    p(e, "jmp %s", end_label);
    p(e, "%s:", else_label);

    if (if_statement->else_statements != NULL)
        emit_statements(e, if_statement->else_statements, if_statement->else_statement_count);

    p(e, "%s:", end_label);
}

void emit_while_statement(Emitter *e, WhileStatement *while_statement) {
    char *start_label = new_label(e);
    char *end_label = new_label(e);

    p(e, "%s:", start_label);
    emit_expression(e, while_statement->condition);
    p(e, "pop rax");
    p(e, "test rax, rax");
    p(e, "jz %s", end_label);

    emit_statements(e, while_statement->statements, while_statement->statement_count);

    p(e, "jmp %s", start_label);
    p(e, "%s:", end_label);
}

void emit_function(Emitter *e, Function *function) {
    p_back(e, "%s:", function->name);
    p_back(e, "push rbp");
    p_back(e, "mov rbp, rsp");
    p_back(e, "sub rsp, %d", function->parameter_count * 16);
    char **temp_symbols = e->symbols;
    size_t temp_symbol_count = e->symbol_count;
    char *symbols[0x100];
    e->symbols = symbols;
    e->symbol_count = 0;
    for (size_t i = 0; i < function->parameter_count; i++) {
        p_back(e, "mov [rbp-%d], %s", (i + 1) * 16, call_registers[i]);
        push_symbol(e, function->parameters[i]);
    }
    char *temp_head = e->head;
    e->head = e->back_head;
    emit_statements(e, function->statements, function->statement_count);
    e->symbols = temp_symbols;
    e->symbol_count = temp_symbol_count;
    e->back_head = e->head;
    e->head = temp_head;
    p_back(e, "leave");
    p_back(e, "ret");
}

void emit_return(Emitter *e, ReturnStatement *return_statement) {
    emit_expression(e, return_statement->expression);
    p(e, "pop rax");
    p(e, "leave");
    p(e, "ret");
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
            case FUNCTION:
                emit_function(e, s->as.function);
                break;
            case RETURN_STATEMENT:
                emit_return(e, s->as.return_statement);
                break;
            default:
                fprintf(stderr, "Expected a statement but found %d\n", s->kind);
                exit(1);
                break;
        }
    }
}

void emit_strings(Emitter *e) {
    for (int i = 0; i < e->string_count; i++) {
        pn(e, "_LD%d db ", i);
        char *str = e->strings[i];
        while (*str != '\0') {
            pn(e, "%d, ", *str++);
        }
        pn(e, "0\n");
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

    emit_strings(e);
}

typedef enum {
    T_EOF,
    T_LET,
    T_IDENT,
    T_EQUALS,
    T_INTLIT,
    T_STRLIT,
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
    T_AND,
    T_OR,
    T_SEMICOLON,
    T_NEWLINE,
    T_LPAREN,
    T_RPAREN,
    T_COMMA,
    T_EXTERN,
    T_IF,
    T_ELSE,
    T_WHILE,
    T_LCURLY,
    T_RCURLY,
    T_FN,
    T_RETURN,
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

FunctionCall *parse_function_call(Parser *p);
Expression *parse_expression(Parser *p);

Expression *parse_factor(Parser *p) {
    Expression *expr = malloc(sizeof(Expression));

    Token t = peek(p);
    switch (t.kind) {
        case T_INTLIT:
            next(p);
            expr->kind = EXPR_NUMBER;
            expr->as.number = t.value.l;
            break;
        case T_IDENT:
            if (peekn(p, 1).kind == T_LPAREN) {
                expr->kind = EXPR_FUNCTION_CALL;
                expr->as.function_call = parse_function_call(p);
            } else {
                next(p);
                expr->kind = EXPR_IDENT;
                expr->as.ident = t.value.s;
            }
            break;
        case T_STRLIT:
            next(p);
            expr->kind = EXPR_STRING;
            expr->as.string = t.value.s;
            break;
        case T_LPAREN:
            next(p);
            free(expr);
            expr = parse_expression(p);
            require(p, T_RPAREN);
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

Expression *parse_additive(Parser *p) {
    Expression *left = parse_term(p);

    while (peek(p).kind == T_PLUS || peek(p).kind == T_MINUS) {
        Token t = next(p);

        Expression *op = malloc(sizeof(Expression));

        op->kind = t.kind == T_PLUS ? EXPR_ADD : EXPR_SUB;
        op->as.binop.left = left;
        op->as.binop.right = parse_term(p);

        left = op;
    }

    return left;
}

Expression *parse_condition(Parser *p) {

    Expression *left = parse_additive(p);

    ExpressionKind kind;

    Token t = peek(p);
    switch (t.kind) {
        case T_LT:
            kind = EXPR_LT;
            break;
        case T_LTE:
            kind = EXPR_LTE;
            break;
        case T_GT:
            kind = EXPR_GT;
            break;
        case T_GTE:
            kind = EXPR_GTE;
            break;
        case T_EQ:
            kind = EXPR_EQ;
            break;
        case T_NEQ:
            kind = EXPR_NEQ;
            break;
        default:
            return left;
    }

    next(p);

    Expression *op = malloc(sizeof(Expression));

    op->kind = kind;
    op->as.binop.left = left;
    op->as.binop.right = parse_additive(p);

    return op;
}

Expression *parse_and_expression(Parser *p) {
    Expression *left = parse_condition(p);

    while (peek(p).kind == T_AND) {
        next(p);

        Expression *op = malloc(sizeof(Expression));

        op->kind = EXPR_AND;
        op->as.binop.left = left;
        op->as.binop.right = parse_condition(p);

        left = op;
    }

    return left;
}

Expression *parse_expression(Parser *p) {
    Expression *left = parse_and_expression(p);

    while (peek(p).kind == T_OR) {
        next(p);

        Expression *op = malloc(sizeof(Expression));

        op->kind = EXPR_OR;
        op->as.binop.left = left;
        op->as.binop.right = parse_and_expression(p);

        left = op;
    }

    return left;
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
    require(p, T_RPAREN);

    call->argument_count = arg_count;


    return call;
}

size_t parse(Parser *p, Statement **program);
Statement *parse_statement(Parser *p);

IfStatement *parse_if_statement(Parser *p) {
    IfStatement *ifs = malloc(sizeof(IfStatement));

    require(p, T_IF);
    ifs->condition = parse_expression(p);
    require(p, T_LCURLY);
    Statement **body_statements = malloc(sizeof(Statement*) * 100);
    size_t body_statement_count = parse(p, body_statements);

    ifs->body_statements = body_statements;
    ifs->body_statement_count = body_statement_count;

    require(p, T_RCURLY);

    if (peek(p).kind == T_ELSE) {
        require(p, T_ELSE);
        if (peek(p).kind == T_IF) {
            Statement **else_statements = malloc(sizeof(Statement*) * 1);

            else_statements[0] = parse_statement(p);

            ifs->else_statements = else_statements;
            ifs->else_statement_count = 1;
        } else {
            require(p, T_LCURLY);
            Statement **else_statements = malloc(sizeof(Statement*) * 100);
            size_t else_statement_count = parse(p, else_statements);

            ifs->else_statements = else_statements;
            ifs->else_statement_count = else_statement_count;
            require(p, T_RCURLY);
        }
    } else ifs->else_statements = NULL;

    return ifs;
}

WhileStatement *parse_while_statement(Parser *p) {
    WhileStatement *whil = malloc(sizeof(WhileStatement));

    require(p, T_WHILE);
    whil->condition = parse_expression(p);
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

Function *parse_function(Parser *p) {
    Function *func = malloc(sizeof(Function));

    require(p, T_FN);
    Token name = require(p, T_IDENT);
    require(p, T_LPAREN);
    char **parameters = malloc(sizeof(char*) * 8);
    size_t parameter_count = 0;
    while (peek(p).kind != T_RPAREN) {
        Expression *expr = parse_factor(p);
        if (expr->kind != EXPR_IDENT) {
            fprintf(stderr, "Expected function parameter to be an identifier\n");
            exit(1);
        }
        parameters[parameter_count++] = expr->as.ident;
        if (peek(p).kind != T_RPAREN) require(p, T_COMMA);
    }
    require(p, T_RPAREN);

    require(p, T_LCURLY);
    Statement **statements = malloc(sizeof(Statement*) * 200);
    size_t statement_count = parse(p, statements);
    require(p, T_RCURLY);

    func->name = name.value.s;
    func->parameters = parameters;
    func->parameter_count = parameter_count;
    func->statements = statements;
    func->statement_count = statement_count;

    return func;
}

ReturnStatement *parse_return_statement(Parser *p) {
    ReturnStatement *ret = malloc(sizeof(ReturnStatement));

    require(p, T_RETURN);
    ret->expression = parse_expression(p);

    return ret;
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
                if (peekn(p, 1).kind == T_LPAREN) {
                    s->kind = FUNCTION_CALL;
                    s->as.function_call = parse_function_call(p);
                } else {
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
        case T_FN:
            s->kind = FUNCTION;
            s->as.function = parse_function(p);
            break;
        case T_RETURN:
            s->kind = RETURN_STATEMENT;
            s->as.return_statement = parse_return_statement(p);
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

    while (c == '/' && l_peek(l) == '/') {
        c = l_next(l);
        while (c != '\n') c = l_next(l);
    }
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
    if (c == '&' && l_peek(l) == '&') {
        l_next(l);
        return (Token){T_AND, {0}};
    }
    if (c == '|' && l_peek(l) == '|') {
        l_next(l);
        return (Token){T_OR, {0}};
    }
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

    if (c == '"') {

        char *strlit = calloc(1, sizeof(char) * 0x1000);

        int i = 0;
        while (1) {
            char n = l_next(l);
            if (n == '"') break;
            else if (n == '\\') {
                char nn = l_next(l);
                if (nn == '"') {
                    strlit[i++] = '\\';
                    strlit[i++] = '"';
                }
                if (nn == 'n') {
                    strlit[i++] = '\n';
                }
            } else {
                strlit[i++] = n;
            }
        }

        strlit[i] = '\0';

        return (Token){T_STRLIT, { .s = strlit }};
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

    if (!isalnum(c) && c != '_') {
        fprintf(stderr, "Unexpected character %c at byte %ld\n", c, l->head-l->base);
        exit(1);
    }

    char *token = calloc(1, sizeof(char) * 0x100);

    token[0] = c;

    int i = 1;
    while (isalnum(l_peek(l)) || l_peek(l) == '_') {
        token[i++] = l_next(l);
    }

    if (strcmp(token, "let") == 0) return (Token){T_LET, {0}};
    if (strcmp(token, "extern") == 0) return (Token){T_EXTERN, {0}};
    if (strcmp(token, "if") == 0) return (Token){T_IF, {0}};
    if (strcmp(token, "else") == 0) return (Token){T_ELSE, {0}};
    if (strcmp(token, "while") == 0) return (Token){T_WHILE, {0}};
    if (strcmp(token, "fn") == 0) return (Token){T_FN, {0}};
    if (strcmp(token, "return") == 0) return (Token){T_RETURN, {0}};

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

    char *code = calloc(1, (size+1)*sizeof(char));
    fread(code, 1, size, fp);
    fclose(fp);
    
    Token tokens[0x10000];
    Lexer l = {code, code};
    size_t token_count = lex(&l, tokens);

    Statement *program[0x1000];
    Parser p = {tokens, tokens + token_count};
    size_t statement_count = parse(&p, program);

    char assembly[0x100000] = {0};
    char back_assembly[0x100000] = {0};
    char *symbols[0x100];
    char *string_labels[0x100];
    Emitter e = {assembly, assembly, back_assembly, back_assembly, symbols, 0, 0, string_labels, 0};
    emit(&e, program, statement_count);

    char *asm_filename = replace_ext(filename, ".asm");

    FILE *asm_fp = fopen(asm_filename, "w");
    fputs(assembly, asm_fp);
    fputs(back_assembly, asm_fp);
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
