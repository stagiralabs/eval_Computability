// Lean compiler output
// Module: Mathlib.Computability.Partrec
// Imports: Init VerifiedAgora.tagger Mathlib.Computability.Primrec Mathlib.Data.Nat.PSub Mathlib.Data.PFun
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
static lean_object* l_Nat_rfindOpt___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Nat_rfind(lean_object*);
lean_object* l_Part_ofOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_rfindX(lean_object*, lean_object*);
static lean_object* l_Nat_rfindOpt___rarg___lambda__1___closed__3;
lean_object* l_Part_bind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_rfind___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Nat_rfindOpt___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Nat_rfindOpt(lean_object*);
LEAN_EXPORT lean_object* l___private_Batteries_WF_0__WellFounded_fixC___at_Nat_rfindX___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_rfindOpt___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg___lambda__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Batteries_WF_0__WellFounded_fixC___at_Nat_rfindX___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Nat_rfindX(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Batteries_WF_0__WellFounded_fixC___at_Nat_rfindX___spec__1(x_1, x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_rfind___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Batteries_WF_0__WellFounded_fixC___at_Nat_rfindX___spec__1(x_1, x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_rfind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_rfind___elambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_rfindOpt___rarg___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_rfindOpt___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_rfindOpt___rarg___lambda__1___closed__1;
x_2 = l_Part_ofOption___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_rfindOpt___rarg___lambda__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Nat_rfindOpt___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_rfindOpt___rarg___lambda__1___closed__3;
x_2 = l_Part_ofOption___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Nat_rfindOpt___rarg___lambda__1___closed__2;
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_Nat_rfindOpt___rarg___lambda__1___closed__4;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = l_Part_ofOption___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_rfindOpt___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Nat_rfindOpt___rarg___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Nat_rfind___elambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_alloc_closure((void*)(l_Nat_rfindOpt___rarg___lambda__2), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Part_bind___rarg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_rfindOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_rfindOpt___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Computability_Primrec(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_PSub(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_PFun(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Computability_Partrec(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Computability_Primrec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_PSub(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_PFun(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_rfindOpt___rarg___lambda__1___closed__1 = _init_l_Nat_rfindOpt___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Nat_rfindOpt___rarg___lambda__1___closed__1);
l_Nat_rfindOpt___rarg___lambda__1___closed__2 = _init_l_Nat_rfindOpt___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Nat_rfindOpt___rarg___lambda__1___closed__2);
l_Nat_rfindOpt___rarg___lambda__1___closed__3 = _init_l_Nat_rfindOpt___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Nat_rfindOpt___rarg___lambda__1___closed__3);
l_Nat_rfindOpt___rarg___lambda__1___closed__4 = _init_l_Nat_rfindOpt___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Nat_rfindOpt___rarg___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
