-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Packed.Internal.Signatures
-- Copyright   :  (c) Alberto Ruiz 2009
-- License     :  GPL-style
--
-- Maintainer  :  Alberto Ruiz <aruiz@um.es>
-- Stability   :  provisional
-- Portability :  portable (uses FFI)
--
-- Signatures of the C functions.
--
-----------------------------------------------------------------------------

module Data.Packed.Internal.Signatures where

import Foreign.Ptr(Ptr)
import Data.Complex(Complex)
import Foreign.C.Types(CInt)

type PF = Ptr Float                             --
type PD = Ptr Double                            --
type PQ = Ptr (Complex Float)                   --
type PC = Ptr (Complex Double)                  --
type TF = CInt -> PF -> IO CInt                 --
type TFF = CInt -> PF -> TF                     --
type TFV = CInt -> PF -> TV                     --
type TVF = CInt -> PD -> TF                     --
type TFFF = CInt -> PF -> TFF                   --
type TV = CInt -> PD -> IO CInt                 --
type TVV = CInt -> PD -> TV                     --
type TVVV = CInt -> PD -> TVV                   --
type TFM = CInt -> CInt -> PF -> IO CInt        --
type TFMFM =  CInt -> CInt -> PF -> TFM         --
type TFMFMFM =  CInt -> CInt -> PF -> TFMFM     --
type TM = CInt -> CInt -> PD -> IO CInt         --
type TMM =  CInt -> CInt -> PD -> TM            --
type TVMM = CInt -> PD -> TMM                   --
type TMVMM = CInt -> CInt -> PD -> TVMM         --
type TMMM =  CInt -> CInt -> PD -> TMM          --
type TVM = CInt -> PD -> TM                     --
type TVVM = CInt -> PD -> TVM                   --
type TMV = CInt -> CInt -> PD -> TV             --
type TMMV = CInt -> CInt -> PD -> TMV           --
type TMVM = CInt -> CInt -> PD -> TVM           --
type TMMVM = CInt -> CInt -> PD -> TMVM         --
type TCM = CInt -> CInt -> PC -> IO CInt        --
type TCVCM = CInt -> PC -> TCM                  --
type TCMCVCM = CInt -> CInt -> PC -> TCVCM      --
type TMCMCVCM = CInt -> CInt -> PD -> TCMCVCM   --
type TCMCMCVCM = CInt -> CInt -> PC -> TCMCVCM  --
type TCMCM = CInt -> CInt -> PC -> TCM          --
type TVCM = CInt -> PD -> TCM                   --
type TCMVCM = CInt -> CInt -> PC -> TVCM        --
type TCMCMVCM = CInt -> CInt -> PC -> TCMVCM    --
type TCMCMCM = CInt -> CInt -> PC -> TCMCM      --
type TCV = CInt -> PC -> IO CInt                --
type TCVCV = CInt -> PC -> TCV                  --
type TCVCVCV = CInt -> PC -> TCVCV              --
type TCVV = CInt -> PC -> TV                    --
type TQV = CInt -> PQ -> IO CInt                --
type TQVQV = CInt -> PQ -> TQV                  --
type TQVQVQV = CInt -> PQ -> TQVQV              --
type TQVF = CInt -> PQ -> TF                    --
type TQM = CInt -> CInt -> PQ -> IO CInt        --
type TQMQM = CInt -> CInt -> PQ -> TQM          --
type TQMQMQM = CInt -> CInt -> PQ -> TQMQM      --
type TCMCV = CInt -> CInt -> PC -> TCV          --
type TVCV = CInt -> PD -> TCV                   --
type TCVM = CInt -> PC -> TM                    --
type TMCVM = CInt -> CInt -> PD -> TCVM         --
type TMMCVM = CInt -> CInt -> PD -> TMCVM       --
