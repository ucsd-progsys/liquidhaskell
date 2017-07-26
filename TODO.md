# TODO

## Proper Encoding of DataTypes

* https://github.com/ucsd-progsys/liquidhaskell/issues/1048

  - fix `symEnv` constructor
  -

* DEPRECATE `makeSmtContext`, `makeSmtEnv` and `symEnv`
  - all that instantiate stuff should work on SInfo
  - OR at the VC level.

* We need to add stuff to the LHS of an SimpC
  - tricky as there _is_ no LHS.
  - lets add reftBind field.
