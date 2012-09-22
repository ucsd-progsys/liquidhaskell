/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    msmt.h

Abstract:

    Z3 API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:
    
--*/

#ifndef _Z3__H_
#define _Z3__H_

#include <stdio.h>

#ifndef __in
#define __in
#endif

#ifndef __in_z
#define __in_z __in
#endif

#ifndef __out
#define __out
#endif

#ifndef __out_z
#define __out_z
#endif

#ifndef __ecount
#define __ecount(num_args)
#endif 

#ifndef __in_ecount
#define __in_ecount(num_args) __in __ecount(num_args)
#endif 

#ifndef __out_ecount
#define __out_ecount(num_args) __out __ecount(num_args)
#endif 

#ifndef __inout_ecount
#define __inout_ecount(num_args) __in __out __ecount(num_args)
#endif 

#ifndef __inout
#define __inout __in __out
#endif

#define Z3_API

#define DEFINE_TYPE(T) typedef struct _ ## T *T
#define DEFINE_VOID(T) typedef void* T

#include"z3_api.h"

#endif

