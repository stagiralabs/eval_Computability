// Lean compiler output
// Module: Mathlib.Computability.Tape
// Imports: Init VerifiedAgora.tagger Mathlib.Data.Vector.Basic Mathlib.Logic.Function.Iterate Mathlib.Order.Basic Mathlib.Tactic.ApplyFun Mathlib.Data.List.GetD
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
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Turing_proj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_above(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Turing_instInhabitedDir;
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_nth(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_getD___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_inhabited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_setoid___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_proj___elambda__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___rarg(lean_object*);
static lean_object* l_Turing_ListBlank_flatMap___rarg___closed__1;
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_inhabited(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_inhabited___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_write___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_write___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Turing_Dir_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Turing_Tape_move___rarg(lean_object*, uint8_t, lean_object*);
lean_object* l_List_tail___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Turing_proj___elambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_toCtorIdx(uint8_t);
LEAN_EXPORT uint8_t l_Turing_instDecidableEqDir(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Turing_ListBlank_append___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Turing_Dir_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_head___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_headI___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_map___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_nth___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_flatMapTR_go___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_move___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_move(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons___boxed(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_head___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_append(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_instDecidableEqDir___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_proj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_below(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankRel_setoid(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_nth___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_head(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Turing_Tape_nth___rarg___closed__1;
LEAN_EXPORT lean_object* l_Turing_ListBlank_hasEmptyc___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_proj___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_map___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_write(lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_append___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_hasEmptyc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Dir_toCtorIdx___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_map___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Turing_Tape_inhabited(lean_object*);
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_lengthTRAux___rarg(x_1, x_5);
x_7 = l_List_lengthTRAux___rarg(x_2, x_5);
x_8 = lean_nat_dec_le(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Turing_BlankExtends_above___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_BlankExtends_above___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankExtends_above___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_BlankExtends_above(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthTRAux___rarg(x_1, x_4);
x_6 = l_List_lengthTRAux___rarg(x_2, x_4);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_above(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_BlankRel_above___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_BlankRel_above___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_above___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_BlankRel_above(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthTRAux___rarg(x_1, x_4);
x_6 = l_List_lengthTRAux___rarg(x_2, x_4);
x_7 = lean_nat_dec_le(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_below(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_BlankRel_below___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_BlankRel_below___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_below___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_BlankRel_below(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_setoid(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_BlankRel_setoid___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_BlankRel_setoid(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_inhabited___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_inhabited(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_hasEmptyc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_hasEmptyc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_hasEmptyc(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Turing_ListBlank_liftOn___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_liftOn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_ListBlank_liftOn(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_ListBlank_mk___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Turing_ListBlank_mk___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_mk(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_head___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_headI___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_head(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_ListBlank_head___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_head___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_head___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_tail___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_ListBlank_tail___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Turing_ListBlank_tail___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_tail___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_tail(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_ListBlank_cons___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_cons___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_ListBlank_cons(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_getD___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_ListBlank_nth___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_nth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_ListBlank_nth___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = l_List_headI___rarg(x_1, x_4);
x_10 = l_List_tail___rarg(x_4);
x_11 = l_Turing_ListBlank_modifyNth___rarg(x_1, x_2, x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_List_headI___rarg(x_1, x_4);
x_14 = lean_apply_1(x_2, x_13);
x_15 = l_List_tail___rarg(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_ListBlank_modifyNth___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_modifyNth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_ListBlank_modifyNth___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_modifyNth_match__1_splitter(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Turing_instInhabitedPointedMap___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_instInhabitedPointedMap___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_instInhabitedPointedMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_instInhabitedPointedMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Turing_instCoeFunPointedMapForall___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_instCoeFunPointedMapForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_instCoeFunPointedMapForall(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Turing_ListBlank_map___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_ListBlank_map(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_proj___elambda__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_proj___elambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_proj___elambda__1___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_proj___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_proj___elambda__1___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_proj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Turing_proj___rarg), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_proj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_proj(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_append___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Turing_ListBlank_append___rarg(x_1, x_5, x_3);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = l_Turing_ListBlank_append___rarg(x_1, x_8, x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_ListBlank_append___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_append___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_ListBlank_append___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Mathlib_Computability_Tape_0__Turing_ListBlank_append_match__1_splitter(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Turing_ListBlank_flatMap___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Turing_ListBlank_flatMap___rarg___closed__1;
x_5 = l_List_flatMapTR_go___rarg(x_2, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Turing_ListBlank_flatMap___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_flatMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_ListBlank_flatMap(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_ListBlank_flatMap___rarg(x_1, x_2, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Turing_ListBlank_bind___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_ListBlank_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Turing_ListBlank_bind(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_inhabited___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Turing_Dir_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Turing_Dir_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Turing_Dir_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Dir_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Dir_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Turing_Dir_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Turing_Dir_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Turing_Dir_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Turing_Dir_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Turing_Dir_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Turing_instDecidableEqDir(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Turing_Dir_toCtorIdx(x_1);
x_4 = l_Turing_Dir_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_instDecidableEqDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Turing_instDecidableEqDir(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Turing_instInhabitedDir() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_Tape_left_u2080___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Turing_Tape_left_u2080___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_left_u2080___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_Tape_left_u2080(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Turing_Tape_right_u2080___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Turing_Tape_right_u2080___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_right_u2080___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_Tape_right_u2080(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_move___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_List_headI___rarg(x_1, x_6);
x_9 = l_List_tail___rarg(x_6);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_3, 2, x_10);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = l_List_headI___rarg(x_1, x_12);
x_15 = l_List_tail___rarg(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 2);
x_22 = l_List_headI___rarg(x_1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
x_24 = l_List_tail___rarg(x_21);
lean_dec(x_21);
lean_ctor_set(x_3, 2, x_24);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_28 = l_List_headI___rarg(x_1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
x_30 = l_List_tail___rarg(x_27);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_move(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_move___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_move___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Turing_Tape_move___rarg(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_3(x_3, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_3(x_4, x_9, x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg___boxed), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Mathlib_Computability_Tape_0__Turing_Tape_move_match__1_splitter(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_List_headI___rarg(x_1, x_3);
x_5 = l_List_tail___rarg(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_mk_x27___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_mk_x27___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_mk_x27___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_mk_u2082___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2082___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_mk_u2082___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Turing_Tape_mk_x27___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_mk_u2081___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_mk_u2081___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Turing_Tape_mk_u2081___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Turing_Tape_nth___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_nth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Turing_Tape_nth___rarg___closed__1;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_nat_abs(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = lean_ctor_get(x_2, 2);
x_12 = l_List_getD___rarg(x_11, x_10, x_1);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_nat_abs(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 1);
x_18 = l_List_getD___rarg(x_17, x_16, x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_nth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_nth___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_nth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_nth___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Turing_Tape_nth___rarg___closed__1;
x_6 = lean_int_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_7 = lean_nat_abs(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_7, x_10);
lean_dec(x_7);
x_12 = lean_apply_1(x_3, x_11);
return x_12;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_nat_abs(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Mathlib_Computability_Tape_0__Turing_Tape_nth_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_write___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_write(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Turing_Tape_write___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_write___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_write___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_2);
x_7 = l_Turing_ListBlank_map___rarg(x_2, x_6);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Turing_ListBlank_map___rarg(x_2, x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Turing_Tape_map___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_map___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_map___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Turing_Tape_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Turing_Tape_map(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_VerifiedAgora_tagger(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Vector_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Logic_Function_Iterate(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Order_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_ApplyFun(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_List_GetD(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mathlib_Computability_Tape(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VerifiedAgora_tagger(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Vector_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Logic_Function_Iterate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_ApplyFun(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_List_GetD(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Turing_ListBlank_flatMap___rarg___closed__1 = _init_l_Turing_ListBlank_flatMap___rarg___closed__1();
lean_mark_persistent(l_Turing_ListBlank_flatMap___rarg___closed__1);
l_Turing_Dir_noConfusion___rarg___closed__1 = _init_l_Turing_Dir_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Turing_Dir_noConfusion___rarg___closed__1);
l_Turing_instInhabitedDir = _init_l_Turing_instInhabitedDir();
l_Turing_Tape_nth___rarg___closed__1 = _init_l_Turing_Tape_nth___rarg___closed__1();
lean_mark_persistent(l_Turing_Tape_nth___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
