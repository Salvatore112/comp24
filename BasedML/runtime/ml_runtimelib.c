#include "ml_runtimelib.h"

int8_t is_ml_ptr(int64_t arg) { return arg & 1; };

#ifndef GC
// temporary solution
void* heap_low_addr = (void*)UINT64_MAX;
void* heap_high_addr = 0;
    #define START_COLOR 0
#endif

int8_t is_inside_heap(int64_t ptr) {
#ifdef GC
    // some GC_code
#else
    return (((uint64_t)heap_low_addr <= (uint64_t)ptr) && ((uint64_t)ptr < (uint64_t)heap_high_addr));
#endif
};

void* ml_malloc(size_t size) {
#ifdef GC
    // some GC_code
#else
    void* res_addr = malloc(size);
    heap_low_addr = (heap_low_addr < res_addr) ? heap_low_addr : res_addr;
    void* high_addr = size + res_addr;
    heap_high_addr = (heap_high_addr > high_addr) ? heap_high_addr : high_addr;
    return res_addr;
#endif
};

box_t* get_box_t(int64_t ptr) { return (box_t*)ptr; };

box_t* create_box_t(size_t size) {
    if (size % 8 != 0)
        size += 8 - (size % 8);

    box_t* res_box = ml_malloc(size);
    res_box->header.color = START_COLOR;
    res_box->header.size = size / 8;
    return res_box;
}

typedef struct {
    int64_t val;
    int64_t next;
} cons_t;

int64_t create_cons(int64_t data, int64_t next) {
    box_t* cons_box = create_box_t(sizeof(box_header_t) + sizeof(cons_t));
    cons_box->header.tag = T_CONS;
    cons_t* cons = (cons_t*)(&(cons_box->values));
    cons->val = data;
    cons->next = next;
    return cons_box;
}

int64_t create_tuple(int64_t tuple_size, ...) {
    va_list list;
    va_start(list, tuple_size);

    box_t* tuple_box = create_box_t(sizeof(box_header_t) + sizeof(tuple_size * 8));
    tuple_box->header.tag = T_TUPLE;

    for (int i = 0; i < tuple_size; i++)
        tuple_box->values[i] = va_arg(list, int64_t);

    va_end(list);

    return tuple_box;
}

typedef struct {
    int64_t fun;
    int64_t args_num;
    int64_t args_applied;
    int64_t applied_args[];
} closure_t;

int64_t create_tuple(int64_t tuple_size, ...) {
    va_list list;
    va_start(list, tuple_size);

    box_t* tuple_box = create_box_t(sizeof(box_header_t) + sizeof(tuple_size * 8));
    tuple_box->header.tag = T_TUPLE;

    for (int i = 0; i < tuple_size; i++)
        tuple_box->values[i] = va_arg(list, int64_t);

    va_end(list);

    return tuple_box;
}