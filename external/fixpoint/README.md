Compiling Without Z3
====================

To build on on platforms WITHOUT Z3, do this:

	% cp tpNull.ml.noz3 tpNull.ml

and then

	% make


To build on the mac (no Z3), do 

	% make -f Makefile.mac

To build on platforms WITH Z3, do this:

	% cp tpNull.ml.z3 tpNull.ml
	% make




Constraint Files
================

The general format of a constraint file is:

  [SUBTYPING CONSTRAINTS]

  [WELL-FORMEDNESS CONSTRAINTS]
  
  [SOLUTIONS]
  
Subtyping Constraints
---------------------

A subtyping constraint has the form

  constraint:
    env[BINDINGS]
    grd PREDICATE
    lhs REFTYPE
    rhs REFTYPE
    id INT tag INT_LIST
    
The BINDINGS are a list of semicolon-separated name, REFTYPE
pairs. The guard PREDICATE is a standard predicate. The integer ID is
used to identify this constraint in error messages, etc.  The INT_LIST
is used as a hook into constraint ordering: if two constraints are
equal according to the predicate variable dependency graph, the tie is
broken by comparing the tags in lexicographic order.

Refined Types
-------------

A refined type has the form

  {VALUE_VAR : SORT | [PREDICATE_OR_KVARS]}

The VALUE_VAR is an identifier. The SORT is one of int, bool, or ptr.
The list PREDICATE_OR_KVARS is a semicolon-separated list of
predicates and/or kvars (identifiers).

Well-Formedness Constraints
---------------------------

A well-formedness constraint has the form

  wf:
    env[BINDINGS]
    reft REFTYPE

Solutions
---------

A solution assigns a predicate variable to a semicolon-separated list
of predicates:

  solution: KVAR := [PREDICATES]
