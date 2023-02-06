- Verification of Libraries
  - [zlib](https://hackage.haskell.org/package/zlib)
  - [probability](https://github.com/nikivazou/probability)

- fix parser error message
  - Add list of reserved tokens

- Applying data type with wrong number of abstract refinement params could give better errors [#297](https://github.com/ucsd-progsys/liquidhaskell/issues/297)

- Export qualifiers from measure types [#302](https://github.com/ucsd-progsys/liquidhaskell/issues/302)

- systematically remove all error calls

 NV: Not sure how easy this is, as it requires deep understanding of the code
    to distinguish dead code from our errors.
