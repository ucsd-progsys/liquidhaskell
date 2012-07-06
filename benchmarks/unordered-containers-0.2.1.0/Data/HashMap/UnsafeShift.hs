{-# LANGUAGE MagicHash #-}

module Data.HashMap.UnsafeShift
    ( unsafeShiftL
    , unsafeShiftR
    ) where

import GHC.Exts (Word(W#), Int(I#), uncheckedShiftL#, uncheckedShiftRL#)

unsafeShiftL :: Word -> Int -> Word
unsafeShiftL (W# x#) (I# i#) = W# (x# `uncheckedShiftL#` i#)
{-# INLINE unsafeShiftL #-}

unsafeShiftR :: Word -> Int -> Word
unsafeShiftR (W# x#) (I# i#) = W# (x# `uncheckedShiftRL#` i#)
{-# INLINE unsafeShiftR #-}
