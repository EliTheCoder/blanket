#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>

typedef struct {
    long value;
} IntLit;

typedef struct Add {
    IntLit *intlit;
    struct Add *expression;
} Add;

typedef struct {
    char *name;
    Add *expression;
} Declaration;

typedef struct {
    char *function_name;
    Add **arguments;
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

void emit_intlit(Emitter *e, IntLit *intlit) {
    p(e, "push %ld", intlit->value);
}

void emit_expression(Emitter *e, Add *expression) {
    emit_intlit(e, expression->intlit);

    if (expression->expression == NULL) return;

    emit_expression(e, expression->expression);

    p(e, "pop rbx");
    p(e, "pop rax");
    p(e, "add rax, rbx");
    p(e, "push rax");
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

    p(e, "call %s", function_call->function_name);
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
                fprintf(stderr, "some shit not implemented");
                exit(1);
                break;
        }
    }
}

int main(void) {
    Statement *program[] = {
        &(Statement){
            .kind = DECLARATION,
            .as = {
                .declaration = &(Declaration){
                    .name = "x",
                    .expression = &(Add){
                        .intlit = &(IntLit){ 34 },
                        .expression = &(Add){
                            .intlit = &(IntLit){ 35 },
                            .expression = NULL
                        }
                    }
                }
            }
        },
        &(Statement){
            .kind = FUNCTION_CALL,
            .as = {
                .function_call = &(FunctionCall){
                    .function_name = "exit",
                    .arguments = (Add*[]){
                        &(Add){
                            .intlit = &(IntLit){ 67 },
                            .expression = NULL
                        }
                    },
                    .argument_count = 1
                }
            }
        }
    };

    char buffer[0x100000] = {0};

    Emitter e = {buffer, buffer};

    emit( &e, program, 2 );

    printf("%s", buffer);
}
