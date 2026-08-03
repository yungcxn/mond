#ifndef MONDC_MONDPRE_H
#define MONDC_MONDPRE_H

//path to this folder is the target .mon file
#define MACRO_OP '%'
#define MACRO_END ';'

#define COMMENT_SINGLE '#'
#define COMMENT_MULTI_BEGIN_1 '/'
#define COMMENT_MULTI_BEGIN_2 '*'
#define COMMENT_MULTI_END_1 '*'
#define COMMENT_MULTI_END_2 '/'

#define MACRO_INCLUDE "incl"
#define MACRO_NOSTANDARD "nostandard"
#define MACRO_FLAG "flag"
#define MACRO_ISSET "isset"

#define MACRO_GETTER "getter"
#define MACRO_SETTER "setter"
#define MACRO_XETTER "xetter"

#define MAX_FILE_INCLUDES 2048

#endif
