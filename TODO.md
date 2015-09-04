# TODO


## Good

     k__230 := [((VV#229 >= 0), CmpZ(VV#229));((VV#229 < vlen([x#a2tP])), Auto(VV#229, x#a2tP));((0 <= VV#229), Auto0(VV#229))]

     k__257 := [((len([VV#256]) <= len([y#a2tQ])), CmpLen(VV#256, y#a2tQ));((len([VV#256]) >= 0), ListZ0(VV#256))]

## Bad

      $k__257 := true

      $k__230 := VV#229 >= 0 && 0 <= VV#229

## Bad Init

   constant vlen : (func(1, [(Data.Vector.Vector  @(0)); int]))

   constant len : (func(2, [(@(0)  @(1)); int]))
   bind 47 y#a2tQ : {VV#225 : [(Tuple  int  a_a2uw)] | [(len([VV#225]) >= 0)]}
   VV#256 : [(Tuple  int  a_a2uw)]

$k__257 := [VV#256 <= y#a2tQ, VV#256 == y#a2tQ, VV#256 >= y#a2tQ, VV#256 > y#a2tQ, VV#256 < y#a2tQ, VV#256 /= y#a2tQ, 0 == 1]

$k__230 := [VV#229 <= VV#16, VV#229 == 1, VV#229 >= 0, 0 <= VV#229, VV#229 == 0, VV#229 <= 0, VV#229 == VV#16, VV#229 >= VV#16, VV#229 /= 0, VV#229 > VV#16, VV#229 < VV#16, VV#229 /= VV#16, VV#229 > 0, VV#229 < 0, 0 == 1]

FApp (FVar 0)        (FVar 1)
FApp (FTC (TC "[]")) (FApp (FApp (FTC (TC "Tuple")) FInt) (FObj "a"))
