# CHANGES

## NEXT

## 0.3.0.0

- Make interpreted mul and div the default, when `solver = z3`
- Use `higherorder` flag to allow higher order binders into the environment 

## 0.2.2.0

- Added support for theory of Arrays `Map_t`, `Map_select`, `Map_store`

- Added support for theory of Bitvectors -- see `Language.Fixpoint.Smt.Bitvector`

- Added support for string literals

## 0.2.1.0

- Pre-compiled binaries of the underlying ocaml solver are now
  provided for Linux, Mac OSX, and Windows.

  No more need to install Ocaml!

## 0.2.0.0

- Parsing has been improved to require *much* fewer parentheses.

- Experimental support for Z3's theory of real numbers with the `--real` flag.
