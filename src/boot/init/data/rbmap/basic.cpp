// Lean compiler output
// Module: init.data.rbmap.basic
// Imports: init.data.ordering.basic init.coe init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_rbnode_mk__insert__result___rarg___boxed(obj*, obj*);
obj* l_rbnode_fold(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main(obj*, obj*, obj*);
obj* l_rbnode_fold___main(obj*, obj*, obj*);
obj* l_rbmap_rev__fold(obj*, obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_any___main(obj*, obj*);
obj* l_rbnode_balance2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_get__color___main(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_mfold___main(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_max___main___rarg(obj*);
obj* l_rbnode_all___rarg(obj*, obj*);
obj* l_nat_add(obj*, obj*);
obj* l_rbmap;
obj* l_rbmap_insert___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_rbmap_all___main(obj*, obj*, obj*);
obj* l_rbnode_fold___rarg(obj*, obj*, obj*);
obj* l_rbmap_fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main(obj*, obj*, obj*);
obj* l_rbnode_max___rarg(obj*);
obj* l_rbmap_min(obj*, obj*, obj*);
obj* l_rbmap_find__core___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main(obj*, obj*, obj*);
obj* l_rbmap_find(obj*, obj*, obj*);
obj* l_rbmap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_all(obj*, obj*);
obj* l_rbnode_find(obj*, obj*);
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj*, obj*);
obj* l_rbnode_find__core___main(obj*, obj*, obj*);
obj* l_rbnode_min___main___rarg(obj*);
obj* l_mk__rbmap(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj*, obj*);
uint8 l_rbnode_get__color___rarg(obj*);
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_any___main___rarg(obj*, obj*);
obj* l_rbnode_min(obj*, obj*);
obj* l_rbnode_balance1(obj*, obj*);
obj* l_rbmap_of__list(obj*, obj*, obj*);
obj* l_rbnode_depth___main(obj*, obj*);
obj* l_rbnode_find__core___rarg(obj*, obj*, obj*);
obj* l_rbmap_min___main___rarg(obj*);
obj* l_rbmap__of___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr(obj*, obj*, obj*);
obj* l_rbnode_mfold___main(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__4(obj*, obj*, obj*);
uint8 l_rbmap_contains___rarg(obj*, obj*, obj*);
obj* l_rbmap_has__repr___rarg___closed__1;
obj* l_rbnode_rev__fold(obj*, obj*, obj*);
obj* l_rbnode_depth___main___rarg(obj*, obj*);
obj* l_rbnode_balance1__node___main(obj*, obj*);
obj* l_rbmap_fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_find___main(obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__1;
obj* l_rbnode_rev__fold___main(obj*, obj*, obj*);
obj* l_rbmap_to__list___main___rarg(obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_empty___main(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_rbnode_balance2__node___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_contains(obj*, obj*, obj*);
obj* l_rbmap_empty___main___rarg___boxed(obj*);
obj* l_rbnode_find__core(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj*, obj*, obj*);
uint8 l_rbmap_empty___main___rarg(obj*);
obj* l_rbnode_get__color(obj*, obj*);
obj* l_rbmap_any___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap__of(obj*, obj*);
obj* l_rbnode_balance1__node(obj*, obj*);
obj* l_rbnode_all___main___rarg(obj*, obj*);
obj* l_rbnode_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_get__color___rarg___boxed(obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj*, obj*, obj*);
obj* l_rbmap_insert___main(obj*, obj*, obj*);
obj* l_rbmap_fold(obj*, obj*, obj*, obj*);
extern obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__3;
obj* l_rbmap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_get__color___main___rarg___boxed(obj*);
obj* l_rbnode_balance1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_any(obj*, obj*, obj*, obj*);
obj* l_rbmap_find__core___main(obj*, obj*, obj*);
obj* l_rbnode_balance2__node(obj*, obj*);
obj* l_rbnode_mfold___rarg(obj*, obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj*, obj*);
obj* l_rbnode_any___rarg(obj*, obj*);
obj* l_rbmap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_max___main(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj*, obj*, obj*);
obj* l_rbmap_from__list(obj*, obj*);
obj* l_rbnode_lower__bound(obj*, obj*, obj*);
obj* l_rbmap_max(obj*, obj*, obj*);
obj* l_rbmap_to__list(obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__5(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj*, obj*, obj*);
obj* l_rbmap_insert(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj*, obj*, obj*);
uint8 l_rbmap_empty___rarg(obj*);
obj* l_rbmap_lower__bound___main(obj*, obj*, obj*);
obj* l_rbmap_all___rarg(obj*, obj*);
obj* l_rbnode_find__core___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj*, obj*);
obj* l_rbmap_has__repr___rarg(obj*, obj*, obj*);
obj* l_rbnode_depth___rarg(obj*, obj*);
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__2;
obj* l_rbnode_mk__insert__result___main___rarg___boxed(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj*, obj*, obj*);
obj* l_rbmap_from__list___rarg(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj*, obj*, obj*);
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_rbmap_max___rarg(obj*);
obj* l_rbmap_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1__node___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___rarg(obj*, obj*, obj*);
obj* l_rbnode_max(obj*, obj*);
obj* l_rbnode_min___main(obj*, obj*);
obj* l_rbnode_mfold(obj*, obj*, obj*, obj*);
obj* l_rbmap_depth___rarg(obj*, obj*);
obj* l_rbnode_fold___main___rarg(obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main(obj*, obj*);
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj*, obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_depth(obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins(obj*, obj*, obj*);
obj* l_rbmap_depth(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result(obj*, obj*);
obj* l_rbnode_color_decidable__eq___boxed(obj*, obj*);
obj* l_rbnode_all___main(obj*, obj*);
obj* l_rbmap_to__list___main(obj*, obj*, obj*);
obj* l_rbmap_of__list___rarg(obj*, obj*);
obj* l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(obj*, obj*, obj*);
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj*, obj*);
obj* l_rbmap_min___main(obj*, obj*, obj*);
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___rarg(uint8, obj*);
obj* l_rbmap_mfor___rarg(obj*, obj*, obj*);
obj* l_rbnode_any(obj*, obj*);
obj* l_rbmap_all___main___rarg(obj*, obj*);
obj* l_rbmap_find___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_balance2(obj*, obj*);
obj* l_rbnode_ins___rarg(obj*, obj*, obj*, obj*);
uint8 l_rbnode_color_decidable__eq(uint8, uint8);
obj* l_rbnode_insert(obj*, obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_min___rarg(obj*);
obj* l_rbmap_of__list___main___rarg(obj*, obj*);
obj* l_rbmap_lower__bound(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbmap__of___spec__5___rarg(obj*, obj*, obj*);
obj* l_rbnode_max___main(obj*, obj*);
obj* l_rbnode_max___main___rarg(obj*);
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_rbmap_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___rarg(obj*, obj*, obj*);
obj* l_rbmap_of__list___main(obj*, obj*, obj*);
obj* l_rbmap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_rbmap_all(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj*, obj*);
obj* l_rbnode_balance2___main(obj*, obj*);
obj* l_rbmap_any___main___rarg(obj*, obj*);
obj* l_rbmap_empty(obj*, obj*, obj*);
obj* l_rbmap_to__list___rarg(obj*);
obj* l_rbmap_empty___rarg___boxed(obj*);
obj* l_rbnode_lower__bound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1___main(obj*, obj*);
obj* l_rbmap_find__core(obj*, obj*, obj*);
obj* l_rbmap_rev__fold___main(obj*, obj*, obj*, obj*);
obj* l_rbmap_fold___main(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_min___rarg(obj*);
obj* l_rbmap_any___rarg(obj*, obj*);
obj* l_rbmap_find__core___main___rarg(obj*, obj*, obj*);
uint8 l_rbnode_color_decidable__eq(uint8 x_0, uint8 x_1) {
_start:
{
if (x_0 == 0)
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
else
{
if (x_1 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_rbnode_color_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_rbnode_color_decidable__eq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_rbnode_depth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::dec(x_1);
lean::inc(x_0);
x_11 = l_rbnode_depth___main___rarg(x_0, x_5);
lean::inc(x_0);
x_13 = l_rbnode_depth___main___rarg(x_0, x_7);
x_14 = lean::apply_2(x_0, x_11, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_14, x_15);
lean::dec(x_15);
lean::dec(x_14);
return x_16;
}
default:
{
obj* x_19; obj* x_21; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 3);
lean::inc(x_21);
lean::dec(x_1);
lean::inc(x_0);
x_25 = l_rbnode_depth___main___rarg(x_0, x_19);
lean::inc(x_0);
x_27 = l_rbnode_depth___main___rarg(x_0, x_21);
x_28 = lean::apply_2(x_0, x_25, x_27);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_28, x_29);
lean::dec(x_29);
lean::dec(x_28);
return x_30;
}
}
}
}
obj* l_rbnode_depth___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_depth___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_min___main___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_11; obj* x_12; 
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
case 1:
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
default:
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
default:
{
obj* x_19; obj* x_21; obj* x_23; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 2);
lean::inc(x_23);
lean::dec(x_0);
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_27; obj* x_28; 
lean::dec(x_19);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_23);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
case 1:
{
lean::dec(x_21);
lean::dec(x_23);
x_0 = x_19;
goto _start;
}
default:
{
lean::dec(x_21);
lean::dec(x_23);
x_0 = x_19;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_min___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___main___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_min___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_max___main___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
switch (lean::obj_tag(x_7)) {
case 0:
{
obj* x_11; obj* x_12; 
lean::dec(x_7);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
case 1:
{
lean::dec(x_5);
lean::dec(x_3);
x_0 = x_7;
goto _start;
}
default:
{
lean::dec(x_5);
lean::dec(x_3);
x_0 = x_7;
goto _start;
}
}
}
default:
{
obj* x_19; obj* x_21; obj* x_23; 
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 3);
lean::inc(x_23);
lean::dec(x_0);
switch (lean::obj_tag(x_23)) {
case 0:
{
obj* x_27; obj* x_28; 
lean::dec(x_23);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_19);
lean::cnstr_set(x_27, 1, x_21);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
case 1:
{
lean::dec(x_21);
lean::dec(x_19);
x_0 = x_23;
goto _start;
}
default:
{
lean::dec(x_21);
lean::dec(x_19);
x_0 = x_23;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___main___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_max___rarg), 1, 0);
return x_4;
}
}
obj* l_rbnode_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = l_rbnode_fold___main___rarg(x_0, x_5, x_2);
lean::inc(x_0);
x_17 = lean::apply_3(x_0, x_7, x_9, x_15);
x_1 = x_11;
x_2 = x_17;
goto _start;
}
default:
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_29; obj* x_31; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_1, 3);
lean::inc(x_25);
lean::dec(x_1);
lean::inc(x_0);
x_29 = l_rbnode_fold___main___rarg(x_0, x_19, x_2);
lean::inc(x_0);
x_31 = lean::apply_3(x_0, x_21, x_23, x_29);
x_1 = x_25;
x_2 = x_31;
goto _start;
}
}
}
}
obj* l_rbnode_fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_3);
return x_12;
}
case 1:
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_26; obj* x_28; obj* x_29; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 3);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_rbnode_mfold___main___rarg(x_0, x_1, x_13, x_3);
lean::inc(x_22);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg___lambda__1), 7, 6);
lean::closure_set(x_28, 0, x_1);
lean::closure_set(x_28, 1, x_15);
lean::closure_set(x_28, 2, x_17);
lean::closure_set(x_28, 3, x_0);
lean::closure_set(x_28, 4, x_19);
lean::closure_set(x_28, 5, x_22);
x_29 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_26, x_28);
return x_29;
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_43; obj* x_45; obj* x_46; 
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_2, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_2, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_2, 3);
lean::inc(x_36);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_0, 1);
lean::inc(x_39);
lean::inc(x_1);
lean::inc(x_0);
x_43 = l_rbnode_mfold___main___rarg(x_0, x_1, x_30, x_3);
lean::inc(x_39);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg___lambda__1), 7, 6);
lean::closure_set(x_45, 0, x_1);
lean::closure_set(x_45, 1, x_32);
lean::closure_set(x_45, 2, x_34);
lean::closure_set(x_45, 3, x_0);
lean::closure_set(x_45, 4, x_36);
lean::closure_set(x_45, 5, x_39);
x_46 = lean::apply_4(x_39, lean::box(0), lean::box(0), x_43, x_45);
return x_46;
}
}
}
}
obj* l_rbnode_mfold___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_8 = lean::apply_3(x_0, x_1, x_2, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_rbnode_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___rarg), 4, 0);
return x_8;
}
}
obj* l_rbnode_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___rarg), 4, 0);
return x_8;
}
}
obj* l_rbnode_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = l_rbnode_rev__fold___main___rarg(x_0, x_11, x_2);
lean::inc(x_0);
x_17 = lean::apply_3(x_0, x_7, x_9, x_15);
x_1 = x_5;
x_2 = x_17;
goto _start;
}
default:
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_29; obj* x_31; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_1, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_1, 3);
lean::inc(x_25);
lean::dec(x_1);
lean::inc(x_0);
x_29 = l_rbnode_rev__fold___main___rarg(x_0, x_25, x_2);
lean::inc(x_0);
x_31 = lean::apply_3(x_0, x_21, x_23, x_29);
x_1 = x_19;
x_2 = x_31;
goto _start;
}
}
}
}
obj* l_rbnode_rev__fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_rev__fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_16; uint8 x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_8, x_10);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
lean::dec(x_6);
if (x_17 == 0)
{
lean::dec(x_12);
lean::dec(x_0);
return x_16;
}
else
{
lean::dec(x_16);
x_1 = x_12;
goto _start;
}
}
else
{
obj* x_25; uint8 x_26; 
lean::dec(x_16);
lean::inc(x_0);
x_25 = l_rbnode_all___main___rarg(x_0, x_6);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
lean::dec(x_12);
lean::dec(x_0);
return x_25;
}
else
{
lean::dec(x_25);
x_1 = x_12;
goto _start;
}
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_41; uint8 x_42; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_1, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 3);
lean::inc(x_37);
lean::dec(x_1);
lean::inc(x_0);
x_41 = lean::apply_2(x_0, x_33, x_35);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
lean::dec(x_31);
if (x_42 == 0)
{
lean::dec(x_0);
lean::dec(x_37);
return x_41;
}
else
{
lean::dec(x_41);
x_1 = x_37;
goto _start;
}
}
else
{
obj* x_50; uint8 x_51; 
lean::dec(x_41);
lean::inc(x_0);
x_50 = l_rbnode_all___main___rarg(x_0, x_31);
x_51 = lean::unbox(x_50);
if (x_51 == 0)
{
lean::dec(x_0);
lean::dec(x_37);
return x_50;
}
else
{
lean::dec(x_50);
x_1 = x_37;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_all___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_16; uint8 x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_8, x_10);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_20; uint8 x_21; 
lean::dec(x_16);
lean::inc(x_0);
x_20 = l_rbnode_any___main___rarg(x_0, x_6);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
lean::dec(x_20);
x_1 = x_12;
goto _start;
}
else
{
lean::dec(x_12);
lean::dec(x_0);
return x_20;
}
}
else
{
lean::dec(x_6);
if (x_17 == 0)
{
lean::dec(x_16);
x_1 = x_12;
goto _start;
}
else
{
lean::dec(x_12);
lean::dec(x_0);
return x_16;
}
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_41; uint8 x_42; 
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_1, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_1, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 3);
lean::inc(x_37);
lean::dec(x_1);
lean::inc(x_0);
x_41 = lean::apply_2(x_0, x_33, x_35);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; uint8 x_46; 
lean::dec(x_41);
lean::inc(x_0);
x_45 = l_rbnode_any___main___rarg(x_0, x_31);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
lean::dec(x_45);
x_1 = x_37;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_37);
return x_45;
}
}
else
{
lean::dec(x_31);
if (x_42 == 0)
{
lean::dec(x_41);
x_1 = x_37;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_37);
return x_41;
}
}
}
}
}
}
obj* l_rbnode_any___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_balance1___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_3);
x_10 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_5);
lean::cnstr_set(x_10, 3, x_6);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_3, 2);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_3, 3);
lean::inc(x_17);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 x_19 = x_3;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_20 = x_19;
 lean::cnstr_set_tag(x_19, 2);
}
lean::cnstr_set(x_20, 0, x_0);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_11);
x_21 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_4);
lean::cnstr_set(x_21, 2, x_5);
lean::cnstr_set(x_21, 3, x_6);
x_22 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 2, x_15);
lean::cnstr_set(x_22, 3, x_21);
return x_22;
}
default:
{
obj* x_23; obj* x_24; 
x_23 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_2);
lean::cnstr_set(x_23, 3, x_3);
x_24 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_5);
lean::cnstr_set(x_24, 3, x_6);
return x_24;
}
}
}
case 1:
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 3);
lean::inc(x_31);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_33 = x_0;
}
x_36 = lean::box(0);
x_34 = x_36;
goto lbl_35;
lbl_35:
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_38 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_38 = x_33;
 lean::cnstr_set_tag(x_33, 2);
}
lean::cnstr_set(x_38, 0, x_25);
lean::cnstr_set(x_38, 1, x_27);
lean::cnstr_set(x_38, 2, x_29);
lean::cnstr_set(x_38, 3, x_31);
x_39 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_39, 0, x_3);
lean::cnstr_set(x_39, 1, x_4);
lean::cnstr_set(x_39, 2, x_5);
lean::cnstr_set(x_39, 3, x_6);
x_40 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_1);
lean::cnstr_set(x_40, 2, x_2);
lean::cnstr_set(x_40, 3, x_39);
return x_40;
}
}
default:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_41; obj* x_42; 
x_41 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_41, 0, x_0);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_3);
x_42 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
lean::cnstr_set(x_42, 2, x_5);
lean::cnstr_set(x_42, 3, x_6);
return x_42;
}
case 1:
{
obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_43 = lean::cnstr_get(x_3, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_3, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_3, 2);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_3, 3);
lean::inc(x_49);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 x_51 = x_3;
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_51;
 lean::cnstr_set_tag(x_51, 2);
}
lean::cnstr_set(x_52, 0, x_0);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_43);
x_53 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_4);
lean::cnstr_set(x_53, 2, x_5);
lean::cnstr_set(x_53, 3, x_6);
x_54 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_45);
lean::cnstr_set(x_54, 2, x_47);
lean::cnstr_set(x_54, 3, x_53);
return x_54;
}
default:
{
obj* x_55; obj* x_56; 
x_55 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_55, 0, x_0);
lean::cnstr_set(x_55, 1, x_1);
lean::cnstr_set(x_55, 2, x_2);
lean::cnstr_set(x_55, 3, x_3);
x_56 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_4);
lean::cnstr_set(x_56, 2, x_5);
lean::cnstr_set(x_56, 3, x_6);
return x_56;
}
}
}
}
}
}
obj* l_rbnode_balance1___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1___main___rarg), 7, 0);
return x_4;
}
}
obj* l_rbnode_balance1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_rbnode_balance1___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_rbnode_balance1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1___rarg), 7, 0);
return x_4;
}
}
obj* l_rbnode_balance1__node___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 3);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_rbnode_balance1___main___rarg(x_7, x_9, x_11, x_13, x_1, x_2, x_3);
return x_16;
}
default:
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 3);
lean::inc(x_23);
lean::dec(x_0);
x_26 = l_rbnode_balance1___main___rarg(x_17, x_19, x_21, x_23, x_1, x_2, x_3);
return x_26;
}
}
}
}
obj* l_rbnode_balance1__node___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1__node___main___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_balance1__node___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_balance1__node___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_balance1__node(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance1__node___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_balance2___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::inc(x_3);
x_9 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_3);
x_10 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_5);
lean::cnstr_set(x_10, 3, x_9);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_3, 2);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_3, 3);
lean::inc(x_17);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 x_19 = x_3;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_20 = x_19;
 lean::cnstr_set_tag(x_19, 2);
}
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_4);
lean::cnstr_set(x_20, 2, x_5);
lean::cnstr_set(x_20, 3, x_0);
x_21 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_15);
lean::cnstr_set(x_21, 3, x_17);
x_22 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_21);
return x_22;
}
default:
{
obj* x_23; obj* x_24; 
x_23 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_2);
lean::cnstr_set(x_23, 3, x_3);
x_24 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_24, 0, x_6);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_5);
lean::cnstr_set(x_24, 3, x_23);
return x_24;
}
}
}
case 1:
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 3);
lean::inc(x_31);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_33 = x_0;
}
x_36 = lean::box(0);
x_34 = x_36;
goto lbl_35;
lbl_35:
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_38 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_38 = x_33;
 lean::cnstr_set_tag(x_33, 2);
}
lean::cnstr_set(x_38, 0, x_6);
lean::cnstr_set(x_38, 1, x_4);
lean::cnstr_set(x_38, 2, x_5);
lean::cnstr_set(x_38, 3, x_25);
x_39 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_39, 0, x_31);
lean::cnstr_set(x_39, 1, x_1);
lean::cnstr_set(x_39, 2, x_2);
lean::cnstr_set(x_39, 3, x_3);
x_40 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_27);
lean::cnstr_set(x_40, 2, x_29);
lean::cnstr_set(x_40, 3, x_39);
return x_40;
}
}
default:
{
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_41; obj* x_42; 
x_41 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_41, 0, x_0);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_3);
x_42 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_42, 0, x_6);
lean::cnstr_set(x_42, 1, x_4);
lean::cnstr_set(x_42, 2, x_5);
lean::cnstr_set(x_42, 3, x_41);
return x_42;
}
case 1:
{
obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_43 = lean::cnstr_get(x_3, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_3, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_3, 2);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_3, 3);
lean::inc(x_49);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 lean::cnstr_release(x_3, 3);
 x_51 = x_3;
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_51;
 lean::cnstr_set_tag(x_51, 2);
}
lean::cnstr_set(x_52, 0, x_6);
lean::cnstr_set(x_52, 1, x_4);
lean::cnstr_set(x_52, 2, x_5);
lean::cnstr_set(x_52, 3, x_0);
x_53 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_53, 0, x_43);
lean::cnstr_set(x_53, 1, x_45);
lean::cnstr_set(x_53, 2, x_47);
lean::cnstr_set(x_53, 3, x_49);
x_54 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_1);
lean::cnstr_set(x_54, 2, x_2);
lean::cnstr_set(x_54, 3, x_53);
return x_54;
}
default:
{
obj* x_55; obj* x_56; 
x_55 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_55, 0, x_0);
lean::cnstr_set(x_55, 1, x_1);
lean::cnstr_set(x_55, 2, x_2);
lean::cnstr_set(x_55, 3, x_3);
x_56 = lean::alloc_cnstr(2, 4, 0);
lean::cnstr_set(x_56, 0, x_6);
lean::cnstr_set(x_56, 1, x_4);
lean::cnstr_set(x_56, 2, x_5);
lean::cnstr_set(x_56, 3, x_55);
return x_56;
}
}
}
}
}
}
obj* l_rbnode_balance2___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2___main___rarg), 7, 0);
return x_4;
}
}
obj* l_rbnode_balance2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_rbnode_balance2___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_rbnode_balance2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2___rarg), 7, 0);
return x_4;
}
}
obj* l_rbnode_balance2__node___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 3);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_rbnode_balance2___main___rarg(x_7, x_9, x_11, x_13, x_1, x_2, x_3);
return x_16;
}
default:
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_26; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 2);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 3);
lean::inc(x_23);
lean::dec(x_0);
x_26 = l_rbnode_balance2___main___rarg(x_17, x_19, x_21, x_23, x_1, x_2, x_3);
return x_26;
}
}
}
}
obj* l_rbnode_balance2__node___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2__node___main___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_balance2__node___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_balance2__node___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_balance2__node(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_balance2__node___rarg), 4, 0);
return x_4;
}
}
uint8 l_rbnode_get__color___main___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 1;
return x_2;
}
case 1:
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 0;
return x_4;
}
default:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 1;
return x_6;
}
}
}
}
obj* l_rbnode_get__color___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_get__color___main___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_rbnode_get__color___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbnode_get__color___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_rbnode_get__color___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_rbnode_get__color___main___rarg(x_0);
return x_1;
}
}
obj* l_rbnode_get__color(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_get__color___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_rbnode_get__color___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbnode_get__color___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_ins___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_ins(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_mk__insert__result___main___rarg(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_10 = x_1;
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_11 = x_10;
 lean::cnstr_set_tag(x_10, 2);
}
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_8);
return x_11;
}
default:
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
obj* l_rbnode_mk__insert__result___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mk__insert__result___main___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_rbnode_mk__insert__result___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_rbnode_mk__insert__result___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_rbnode_mk__insert__result___rarg(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_mk__insert__result___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_mk__insert__result(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mk__insert__result___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_rbnode_mk__insert__result___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_rbnode_mk__insert__result___rarg(x_2, x_1);
return x_3;
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbnode_insert___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbnode_insert___spec__1___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_find__core___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_26; uint8 x_27; 
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_9, x_2);
x_27 = lean::unbox(x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_2);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_9);
lean::cnstr_set(x_32, 1, x_11);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
lean::dec(x_9);
lean::dec(x_11);
x_1 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_7;
goto _start;
}
}
default:
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_1, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_1, 3);
lean::inc(x_47);
lean::dec(x_1);
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_60; uint8 x_61; 
lean::dec(x_41);
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_60 = lean::apply_2(x_0, x_43, x_2);
x_61 = lean::unbox(x_60);
lean::dec(x_60);
if (x_61 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_47);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_43);
lean::cnstr_set(x_66, 1, x_45);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
lean::dec(x_43);
lean::dec(x_45);
x_1 = x_47;
goto _start;
}
}
else
{
lean::dec(x_43);
lean::dec(x_45);
lean::dec(x_47);
x_1 = x_41;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find__core___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_find__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_3, x_11);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_11, x_3);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_13);
return x_33;
}
else
{
lean::dec(x_13);
x_1 = x_0;
x_2 = x_15;
goto _start;
}
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_9;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 3);
lean::inc(x_46);
lean::dec(x_2);
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_58; uint8 x_59; 
lean::dec(x_40);
lean::inc(x_3);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_42, x_3);
x_59 = lean::unbox(x_58);
lean::dec(x_58);
if (x_59 == 0)
{
obj* x_64; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_44);
return x_64;
}
else
{
lean::dec(x_44);
x_1 = x_0;
x_2 = x_46;
goto _start;
}
}
else
{
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_42);
x_1 = x_0;
x_2 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_rbnode_find___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_5;
}
}
obj* l_rbnode_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_lower__bound___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_7);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_9, x_2);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_2);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_9);
lean::cnstr_set(x_33, 1, x_11);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_9);
lean::cnstr_set(x_35, 1, x_11);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_1 = x_13;
x_3 = x_36;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_7;
goto _start;
}
}
default:
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_54; uint8 x_55; 
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 2);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_1, 3);
lean::inc(x_48);
lean::dec(x_1);
lean::inc(x_44);
lean::inc(x_2);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_2, x_44);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_62; uint8 x_63; 
lean::dec(x_3);
lean::dec(x_42);
lean::inc(x_2);
lean::inc(x_44);
lean::inc(x_0);
x_62 = lean::apply_2(x_0, x_44, x_2);
x_63 = lean::unbox(x_62);
lean::dec(x_62);
if (x_63 == 0)
{
obj* x_68; obj* x_69; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_48);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_44);
lean::cnstr_set(x_68, 1, x_46);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
else
{
obj* x_70; obj* x_71; 
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_44);
lean::cnstr_set(x_70, 1, x_46);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_1 = x_48;
x_3 = x_71;
goto _start;
}
}
else
{
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_48);
x_1 = x_42;
goto _start;
}
}
}
}
}
obj* l_rbnode_lower__bound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___main___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_lower__bound___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_lower__bound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbnode_lower__bound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___rarg), 4, 0);
return x_6;
}
}
obj* _init_l_rbmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_mk__rbmap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
}
obj* l_rbmap_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_depth(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_depth___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___main___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_fold___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_rev__fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___main___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_rev__fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_rev__fold___rarg), 3, 0);
return x_8;
}
}
obj* l_rbmap_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfold___main___rarg), 4, 0);
return x_10;
}
}
obj* l_rbmap_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfold___rarg), 4, 0);
return x_10;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_3);
return x_12;
}
case 1:
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_26; obj* x_28; obj* x_29; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 3);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(x_0, x_1, x_13, x_3);
lean::inc(x_22);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1), 7, 6);
lean::closure_set(x_28, 0, x_0);
lean::closure_set(x_28, 1, x_1);
lean::closure_set(x_28, 2, x_15);
lean::closure_set(x_28, 3, x_17);
lean::closure_set(x_28, 4, x_19);
lean::closure_set(x_28, 5, x_22);
x_29 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_26, x_28);
return x_29;
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; obj* x_43; obj* x_45; obj* x_46; 
x_30 = lean::cnstr_get(x_2, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_2, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_2, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_2, 3);
lean::inc(x_36);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_0, 1);
lean::inc(x_39);
lean::inc(x_1);
lean::inc(x_0);
x_43 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(x_0, x_1, x_30, x_3);
lean::inc(x_39);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1), 7, 6);
lean::closure_set(x_45, 0, x_0);
lean::closure_set(x_45, 1, x_1);
lean::closure_set(x_45, 2, x_32);
lean::closure_set(x_45, 3, x_34);
lean::closure_set(x_45, 4, x_36);
lean::closure_set(x_45, 5, x_39);
x_46 = lean::apply_4(x_39, lean::box(0), lean::box(0), x_43, x_45);
return x_46;
}
}
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 4);
lean::inc(x_10);
lean::inc(x_1);
x_13 = lean::apply_2(x_1, x_2, x_3);
x_14 = lean::cnstr_get(x_8, 1);
lean::inc(x_14);
lean::dec(x_8);
x_17 = lean::box(0);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
x_19 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg), 4, 3);
lean::closure_set(x_20, 0, x_0);
lean::closure_set(x_20, 1, x_1);
lean::closure_set(x_20, 2, x_4);
x_21 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
obj* l_rbnode_mfold___main___at_rbmap_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg), 4, 0);
return x_8;
}
}
obj* l_rbmap_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_mfold___main___at_rbmap_mfor___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_mfor___rarg), 3, 0);
return x_10;
}
}
uint8 l_rbmap_empty___main___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 1;
return x_2;
}
case 1:
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 0;
return x_4;
}
default:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 0;
return x_6;
}
}
}
}
obj* l_rbmap_empty___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___main___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_rbmap_empty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbmap_empty___main___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l_rbmap_empty___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_2; 
lean::dec(x_0);
x_2 = 1;
return x_2;
}
case 1:
{
uint8 x_4; 
lean::dec(x_0);
x_4 = 0;
return x_4;
}
default:
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 0;
return x_6;
}
}
}
}
obj* l_rbmap_empty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_empty___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_rbmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_0);
return x_1;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_9, x_1);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_7);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_0 = x_3;
x_1 = x_14;
goto _start;
}
default:
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 2);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
lean::dec(x_0);
x_25 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_22, x_1);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_20);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_0 = x_16;
x_1 = x_27;
goto _start;
}
}
}
}
obj* l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_rbmap_to__list___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_rbnode_rev__fold___main___at_rbmap_to__list___main___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_to__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_to__list___main___rarg(x_0);
return x_1;
}
}
obj* l_rbmap_to__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_to__list___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_min___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_9);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_rbmap_min___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_9);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_rbmap_min(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_min___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_max___main___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_9);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_rbmap_max___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___main___rarg), 1, 0);
return x_6;
}
}
obj* l_rbmap_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_9);
if (lean::is_scalar(x_6)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_6;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_rbmap_max(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_max___rarg), 1, 0);
return x_6;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_37; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::dec(x_3);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::dec(x_9);
lean::inc(x_1);
lean::inc(x_0);
x_21 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_2, x_11);
x_22 = lean::apply_1(x_0, x_14);
x_23 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_23);
x_25 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_27 = l_list_repr__aux___main___rarg___closed__1;
x_28 = lean::string_append(x_25, x_27);
x_29 = lean::apply_1(x_1, x_16);
x_30 = lean::string_append(x_28, x_29);
lean::dec(x_29);
x_32 = l_option_has__repr___rarg___closed__3;
x_33 = lean::string_append(x_30, x_32);
lean::inc(x_27);
x_35 = lean::string_append(x_27, x_33);
lean::dec(x_33);
x_37 = lean::string_append(x_35, x_21);
lean::dec(x_21);
return x_37;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_42; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_42 = l_string_join___closed__1;
lean::inc(x_42);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_49; obj* x_51; uint8 x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
x_44 = lean::cnstr_get(x_3, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_3, 1);
lean::inc(x_46);
lean::dec(x_3);
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_44, 1);
lean::inc(x_51);
lean::dec(x_44);
x_54 = 0;
lean::inc(x_1);
lean::inc(x_0);
x_57 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_54, x_46);
x_58 = lean::apply_1(x_0, x_49);
x_59 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = l_list_repr__aux___main___rarg___closed__1;
x_64 = lean::string_append(x_61, x_63);
x_65 = lean::apply_1(x_1, x_51);
x_66 = lean::string_append(x_64, x_65);
lean::dec(x_65);
x_68 = l_option_has__repr___rarg___closed__3;
x_69 = lean::string_append(x_66, x_68);
x_70 = lean::string_append(x_69, x_57);
lean::dec(x_57);
return x_70;
}
}
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_list_repr___main___rarg___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
uint8 x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_8 = 1;
x_9 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_8, x_2);
x_10 = l_list_repr___main___rarg___closed__2;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = l_list_repr___main___rarg___closed__3;
x_15 = lean::string_append(x_12, x_14);
return x_15;
}
}
}
obj* l_list_repr___main___at_rbmap_has__repr___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___main___at_rbmap_has__repr___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_rbmap_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbmap_of ");
return x_0;
}
}
obj* l_rbmap_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
x_3 = l_rbmap_to__list___main___rarg(x_2);
x_4 = l_list_repr___main___at_rbmap_has__repr___spec__1___rarg(x_0, x_1, x_3);
x_5 = l_rbmap_has__repr___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_7;
}
}
obj* l_rbmap_has__repr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_has__repr___rarg), 3, 0);
return x_6;
}
}
obj* l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_list_repr__aux___main___at_rbmap_has__repr___spec__2___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_insert___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbmap_insert___main___spec__2___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbmap_insert___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_insert___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_of__list___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbmap_of__list___main___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbmap_of__list___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_of__list___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_of__list___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_of__list___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_0);
x_16 = l_rbmap_of__list___main___rarg(x_0, x_7);
x_17 = l_rbnode_insert___at_rbmap_of__list___main___spec__2___rarg(x_0, x_16, x_10, x_12);
return x_17;
}
}
}
obj* l_rbmap_of__list___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_of__list___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_of__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_of__list___rarg), 2, 0);
return x_6;
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_26; uint8 x_27; 
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_9, x_2);
x_27 = lean::unbox(x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_2);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_9);
lean::cnstr_set(x_32, 1, x_11);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
else
{
lean::dec(x_9);
lean::dec(x_11);
x_1 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_7;
goto _start;
}
}
default:
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_53; uint8 x_54; 
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_1, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_1, 3);
lean::inc(x_47);
lean::dec(x_1);
lean::inc(x_43);
lean::inc(x_2);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_2, x_43);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_60; uint8 x_61; 
lean::dec(x_41);
lean::inc(x_2);
lean::inc(x_43);
lean::inc(x_0);
x_60 = lean::apply_2(x_0, x_43, x_2);
x_61 = lean::unbox(x_60);
lean::dec(x_60);
if (x_61 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_47);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_43);
lean::cnstr_set(x_66, 1, x_45);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
return x_67;
}
else
{
lean::dec(x_43);
lean::dec(x_45);
x_1 = x_47;
goto _start;
}
}
else
{
lean::dec(x_43);
lean::dec(x_45);
lean::dec(x_47);
x_1 = x_41;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find__core___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find__core___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbmap_find__core___main___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_3, x_11);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_11, x_3);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_13);
return x_33;
}
else
{
lean::dec(x_13);
x_1 = x_0;
x_2 = x_15;
goto _start;
}
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_9;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 3);
lean::inc(x_46);
lean::dec(x_2);
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_58; uint8 x_59; 
lean::dec(x_40);
lean::inc(x_3);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_42, x_3);
x_59 = lean::unbox(x_58);
lean::dec(x_58);
if (x_59 == 0)
{
obj* x_64; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_44);
return x_64;
}
else
{
lean::dec(x_44);
x_1 = x_0;
x_2 = x_46;
goto _start;
}
}
else
{
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_42);
x_1 = x_0;
x_2 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_find___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_find___main___spec__1___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_7);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_9, x_2);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_2);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_9);
lean::cnstr_set(x_33, 1, x_11);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_9);
lean::cnstr_set(x_35, 1, x_11);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_1 = x_13;
x_3 = x_36;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_7;
goto _start;
}
}
default:
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_54; uint8 x_55; 
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 2);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_1, 3);
lean::inc(x_48);
lean::dec(x_1);
lean::inc(x_44);
lean::inc(x_2);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_2, x_44);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_62; uint8 x_63; 
lean::dec(x_3);
lean::dec(x_42);
lean::inc(x_2);
lean::inc(x_44);
lean::inc(x_0);
x_62 = lean::apply_2(x_0, x_44, x_2);
x_63 = lean::unbox(x_62);
lean::dec(x_62);
if (x_63 == 0)
{
obj* x_68; obj* x_69; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_48);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_44);
lean::cnstr_set(x_68, 1, x_46);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
else
{
obj* x_70; obj* x_71; 
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_44);
lean::cnstr_set(x_70, 1, x_46);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
x_1 = x_48;
x_3 = x_71;
goto _start;
}
}
else
{
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_48);
x_1 = x_42;
goto _start;
}
}
}
}
}
obj* l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_lower__bound___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_lower__bound___main___at_rbmap_lower__bound___main___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_lower__bound___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___main___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_lower__bound___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_lower__bound___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_lower__bound(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_lower__bound___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_3, x_11);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_11, x_3);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_33; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_13);
return x_33;
}
else
{
lean::dec(x_13);
x_1 = x_0;
x_2 = x_15;
goto _start;
}
}
else
{
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_11);
x_1 = x_0;
x_2 = x_9;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_2, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_2, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_2, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_2, 3);
lean::inc(x_46);
lean::dec(x_2);
lean::inc(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_3, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_58; uint8 x_59; 
lean::dec(x_40);
lean::inc(x_3);
lean::inc(x_0);
x_58 = lean::apply_2(x_0, x_42, x_3);
x_59 = lean::unbox(x_58);
lean::dec(x_58);
if (x_59 == 0)
{
obj* x_64; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_46);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_44);
return x_64;
}
else
{
lean::dec(x_44);
x_1 = x_0;
x_2 = x_46;
goto _start;
}
}
else
{
lean::dec(x_44);
lean::dec(x_46);
lean::dec(x_42);
x_1 = x_0;
x_2 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_rbmap_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_rbmap_contains___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find___main___at_rbmap_contains___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_rbmap_contains___spec__1___rarg), 3, 0);
return x_6;
}
}
uint8 l_rbmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_rbnode_find___main___at_rbmap_contains___spec__2___rarg(x_0, lean::box(0), x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
return x_4;
}
}
obj* l_rbmap_contains(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_contains___rarg___boxed), 3, 0);
return x_6;
}
}
obj* l_rbmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_rbmap_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap_from__list___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbmap_from__list___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbmap_from__list___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap_from__list___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap_from__list___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap_from__list___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_0);
x_16 = l_rbnode_insert___at_rbmap_from__list___spec__2___rarg(x_0, x_1, x_10, x_12);
x_1 = x_16;
x_2 = x_7;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap_from__list___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap_from__list___spec__4___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_from__list___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbmap_from__list___spec__4___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbmap_from__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_all(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_all___rarg), 2, 0);
return x_8;
}
}
obj* l_rbmap_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___main___rarg), 2, 0);
return x_6;
}
}
obj* l_rbmap_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbmap_any(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_any___rarg), 2, 0);
return x_8;
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_6; 
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_15 = x_1;
}
lean::inc(x_9);
lean::inc(x_2);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_2, x_9);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_9, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
if (lean::is_scalar(x_15)) {
 x_31 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_31 = x_15;
}
lean::cnstr_set(x_31, 0, x_7);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_13);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_13, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_7);
lean::cnstr_set(x_33, 1, x_9);
lean::cnstr_set(x_33, 2, x_11);
lean::cnstr_set(x_33, 3, x_32);
return x_33;
}
}
else
{
obj* x_34; obj* x_35; 
x_34 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_7, x_2, x_3);
if (lean::is_scalar(x_15)) {
 x_35 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_35 = x_15;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_11);
lean::cnstr_set(x_35, 3, x_13);
return x_35;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_48; uint8 x_49; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 3);
lean::inc(x_42);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_44 = x_1;
}
lean::inc(x_38);
lean::inc(x_2);
lean::inc(x_0);
x_48 = lean::apply_2(x_0, x_2, x_38);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_54; uint8 x_55; 
lean::inc(x_2);
lean::inc(x_38);
lean::inc(x_0);
x_54 = lean::apply_2(x_0, x_38, x_2);
x_55 = lean::unbox(x_54);
lean::dec(x_54);
if (x_55 == 0)
{
obj* x_60; 
lean::dec(x_0);
lean::dec(x_38);
lean::dec(x_40);
if (lean::is_scalar(x_44)) {
 x_60 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_60 = x_44;
}
lean::cnstr_set(x_60, 0, x_36);
lean::cnstr_set(x_60, 1, x_2);
lean::cnstr_set(x_60, 2, x_3);
lean::cnstr_set(x_60, 3, x_42);
return x_60;
}
else
{
uint8 x_62; 
lean::inc(x_42);
x_62 = l_rbnode_get__color___main___rarg(x_42);
if (x_62 == 0)
{
obj* x_64; obj* x_65; 
lean::dec(x_44);
x_64 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_42, x_2, x_3);
x_65 = l_rbnode_balance2__node___main___rarg(x_64, x_38, x_40, x_36);
return x_65;
}
else
{
obj* x_66; obj* x_67; 
x_66 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_42, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_67 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_67 = x_44;
}
lean::cnstr_set(x_67, 0, x_36);
lean::cnstr_set(x_67, 1, x_38);
lean::cnstr_set(x_67, 2, x_40);
lean::cnstr_set(x_67, 3, x_66);
return x_67;
}
}
}
else
{
uint8 x_69; 
lean::inc(x_36);
x_69 = l_rbnode_get__color___main___rarg(x_36);
if (x_69 == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_44);
x_71 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_36, x_2, x_3);
x_72 = l_rbnode_balance1__node___main___rarg(x_71, x_38, x_40, x_42);
return x_72;
}
else
{
obj* x_73; obj* x_74; 
x_73 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_36, x_2, x_3);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_38);
lean::cnstr_set(x_74, 2, x_40);
lean::cnstr_set(x_74, 3, x_42);
return x_74;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbmap__of___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbmap__of___spec__4___rarg), 4, 0);
return x_6;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbmap__of___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbmap__of___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbmap__of___spec__3___rarg), 4, 0);
return x_6;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbmap__of___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbmap__of___spec__2___rarg), 4, 0);
return x_6;
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_0);
x_16 = l_rbnode_insert___at_rbmap__of___spec__3___rarg(x_0, x_1, x_10, x_12);
x_1 = x_16;
x_2 = x_7;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbmap__of___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbmap__of___spec__5___rarg), 3, 0);
return x_6;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbmap__of___spec__5___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbmap_from__list___at_rbmap__of___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_from__list___at_rbmap__of___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_rbmap_from__list___at_rbmap__of___spec__1___rarg(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* l_rbmap__of(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap__of___rarg), 3, 0);
return x_4;
}
}
void initialize_init_data_ordering_basic();
void initialize_init_coe();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_data_rbmap_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_ordering_basic();
 initialize_init_coe();
 initialize_init_data_option_basic();
 l_rbmap = _init_l_rbmap();
 l_rbmap_has__repr___rarg___closed__1 = _init_l_rbmap_has__repr___rarg___closed__1();
}
