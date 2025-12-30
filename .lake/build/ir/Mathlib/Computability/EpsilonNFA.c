// Lean compiler output
// Module: Mathlib.Computability.EpsilonNFA
// Imports: Init VerifiedAgora.tagger Mathlib.Computability.NFA Mathlib.Data.List.ReduceOption
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
LEAN_EXPORT lean_object* l__u03b5NFA_toNFA(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l__u03b5NFA_instOne(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l__u03b5NFA_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l__u03b5NFA_instZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NFA_to_u03b5NFA___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l__u03b5NFA_toNFA___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NFA_to_u03b5NFA(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l__u03b5NFA_toNFA(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, lean_box(0));
lean_ctor_set(x_4, 1, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l__u03b5NFA_toNFA___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l__u03b5NFA_toNFA(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_NFA_to_u03b5NFA(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, lean_box(0));
lean_ctor_set(x_4, 1, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_NFA_to_u03b5NFA___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_NFA_to_u03b5NFA(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l__u03b5NFA_instZero(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, lean_box(0));
lean_ctor_set(x_3, 1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l__u03b5NFA_instOne(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, lean_box(0));
lean_ctor_set(x_3, 1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l__u03b5NFA_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, lean_box(0));
lean_ctor_set(x_3, 1, lean_box(0));
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_NFA(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_ReduceOption(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Computability_EpsilonNFA(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_NFA(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_ReduceOption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
