#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>
#include <ctype.h>

typedef enum {
    EXPR_NUMBER,
    EXPR_IDENT,
    EXPR_ADD,
} ExpressionKind;

typedef struct Expression {
    ExpressionKind kind;

    union {
        long number;
        char *ident;
        struct {
            struct Expression *left;
            struct Expression *right;
        } add;
    } as;
} Expression;

typedef struct {
    char *name;
    Expression *expression;
} Declaration;

typedef struct {
    char *name;
    Expression **arguments;
    size_t argument_count;
} FunctionCall;

typedef enum {
    DECLARATION,
    FUNCTION_CALL,
} StatementKind;

typedef struct {
    union {
        Declaration *declaration;
        FunctionCall *function_call;
    } as;
    StatementKind kind;
} Statement;

typedef struct {
    char *base;
    char *head;
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

void emit_expression(Emitter *e, Expression *expression) {
    switch (expression->kind) {
        case EXPR_NUMBER:
            p(e, "push %ld", expression->as.number);
            break;
        case EXPR_IDENT:
            p(e, "push %s", expression->as.ident);
            break;
        case EXPR_ADD:
            emit_expression(e, expression->as.add.left);
            emit_expression(e, expression->as.add.right);
            p(e, "pop rbx");
            p(e, "pop rax");
            p(e, "add rax, rbx");
            p(e, "push rax");
            break;
    }
}

void emit_declaration(Emitter *e, Declaration *declaration) {
    p(e, "sub rsp, 8");

    emit_expression(e, declaration->expression);

    p(e, "pop rax");
    p(e, "mov [rsp], rax");
}

void emit_function_call(Emitter *e, FunctionCall *function_call) {
    const char *call_registers[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};

    for (size_t i = 0; i < function_call->argument_count; i++) {
        emit_expression(e, function_call->arguments[i]);
        p(e, "pop %s", call_registers[i]);
    }

    p(e, "call %s", function_call->name);
}

void emit(Emitter *e, Statement **ast, size_t statement_count) {
    FILE *header = fopen("./header.asm", "r");
    fseek(header, 0, SEEK_END);
    long size = ftell(header);
    rewind(header);

    fread(e->head, 1, size, header);
    e->head += size;

    fclose(header);

    for (size_t i = 0; i < statement_count; i++) {
        Statement *s = ast[i];

        switch (s->kind) {
            case DECLARATION:
                emit_declaration(e, s->as.declaration);
                break;
            case FUNCTION_CALL:
                emit_function_call(e, s->as.function_call);
                break;
            default:
                fprintf(stderr, "Expected declaration or function call\n");
                exit(1);
                break;
        }
    }
}

typedef enum {
    T_EOF,
    T_LET,
    T_IDENT,
    T_EQUALS,
    T_INTLIT,
    T_PLUS,
    T_SEMICOLON,
    T_NEWLINE,
    T_LPAREN,
    T_RPAREN,
    T_COMMA,
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

Expression *parse_expression(Parser *p) {
    Expression *left = parse_factor(p);

    while (peek(p).kind == T_PLUS) {
        next(p);

        Expression *right = parse_factor(p);

        Expression *add = malloc(sizeof(Expression));

        add->kind = EXPR_ADD;
        add->as.add.left = left;
        add->as.add.right = right;

        left = add;
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

Statement *parse_statement(Parser *p) {
    Statement *s = malloc(sizeof(Statement));

    switch (peek(p).kind) {
        case T_LET:
            s->kind = DECLARATION;
            s->as.declaration = parse_declaration(p);
            break;
        case T_IDENT:
            s->kind = FUNCTION_CALL;
            s->as.function_call = parse_function_call(p);
            break;
        default:
            fprintf(stderr, "Expected statement to be either declaration or function call");
            exit(1);
    }

    for (Token x = peek(p); x.kind == T_NEWLINE || x.kind == T_SEMICOLON; x = peek(p))
        next(p);

    return s;
}

size_t parse(Parser *p, Statement **program) {
    int i = 0;
    while (peek(p).kind != T_EOF) {
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
    if (c == '=') return (Token){T_EQUALS, {0}};
    if (c == '+') return (Token){T_PLUS, {0}};
    if (c == ';') return (Token){T_SEMICOLON, {0}};
    if (c == '(') return (Token){T_LPAREN, {0}};
    if (c == ')') return (Token){T_RPAREN, {0}};
    if (c == ',') return (Token){T_COMMA, {0}};

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
        fprintf(stderr, "Unexpected character %c\n", c);
        exit(1);
    }

    char *token = calloc(1, sizeof(char) * 0x100);

    token[0] = c;

    int i = 1;
    while (isalnum(l_peek(l))) {
        token[i++] = l_next(l);
    }

    if (strcmp(token, "let") == 0) {
        return (Token){T_LET, {0}};
    }

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

    char buffer[0x100000] = {0};
    Emitter e = {buffer, buffer};
    emit(&e, program, statement_count);

    printf("%s", buffer);
}
