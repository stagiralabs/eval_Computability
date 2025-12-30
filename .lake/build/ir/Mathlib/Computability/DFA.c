// Lean compiler output
// Module: Mathlib.Computability.DFA
// Imports: Init VerifiedAgora.tagger Mathlib.Computability.Language Mathlib.Data.Countable.Small Mathlib.Data.Fintype.Pigeonhole Mathlib.Tactic.NormNum
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_DFA_comap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg(lean_object*);
LEAN_EXPORT lean_object* l_DFA_comap___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_evalFrom___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___rarg(lean_object*);
LEAN_EXPORT lean_object* l_DFA_evalFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_comap___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Equiv_symm___elambda__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_comap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_eval___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_DFA_instInhabited___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_DFA_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DFA_instInhabited___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DFA_instInhabited___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_DFA_instInhabited___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_evalFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_List_foldl___rarg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_DFA_evalFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DFA_evalFrom___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DFA_eval___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_DFA_evalFrom___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_DFA_eval___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DFA_comap___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_2(x_5, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_DFA_comap___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_DFA_comap___elambda__1___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_comap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_DFA_comap___elambda__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
lean_dec(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
lean_ctor_set(x_2, 2, lean_box(0));
lean_ctor_set(x_2, 0, x_3);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_DFA_comap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_DFA_comap___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_apply_1(x_6, x_3);
x_8 = lean_apply_2(x_5, x_7, x_4);
x_9 = l_Equiv_symm___elambda__2___rarg(x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__1___rarg___lambda__1), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Equiv_symm___elambda__2___rarg(x_1, x_4);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__1___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Equiv_symm___elambda__2___rarg(x_2, x_3);
x_7 = lean_apply_2(x_5, x_6, x_4);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__2___rarg___lambda__1), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__2___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__2___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_DFA_reindex___elambda__1___rarg), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DFA_reindex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_DFA_reindex___rarg), 1, 0);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_Language(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Countable_Small(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Pigeonhole(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_NormNum(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Computability_DFA(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_Language(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Countable_Small(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Pigeonhole(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_NormNum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
