#ifndef MONDC_MACROGEN_H
#define MONDC_MACROGEN_H

/*
* needs to be suited for mond syntax
*/

//accessmod typename
#define GETTER1 " get_"
//fieldname
#define GETTER2 "() { \n  return $."
//fieldname
#define GETTER3 ";\n\n"

//accessmod
#define SETTER1 " void set_"
//fieldname
#define SETTER2 "("
//typename
#define SETTER3 " x) {\n  $."
//fieldname
#define SETTER4 " = x;\n\n"


#endif
