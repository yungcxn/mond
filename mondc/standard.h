#ifndef STANDARD_H
#define STANDARD_H

//generated by generatestandard.py

const char standardlibtext[] =
    "%flag USING_STANDARD\n"
    "class Exception {\n"
    "    family string msg;\n"
    "    $init(string msg) {\n"
    "        $.msg = msg;\n"
    "    }\n"
    "}\n"
    "int len(string s){\n"
    "    return (spaceof s);\n"
    "}\n"
    "int len(unistring s){\n"
    "    return (spaceof s) / 2;\n"
    "}\n"
;

#endif