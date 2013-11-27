#define PHASE_STREAM [1]
#define PHASE_INNER  [0]

#define INLINE_STREAM INLINE PHASE_STREAM
#define INLINE_INNER  INLINE PHASE_INNER

#ifndef NOT_VECTOR_MODULE
import qualified Data.Vector.Internal.Check as Ck
#endif

#define ERROR          (Ck.error __FILE__ __LINE__)
#define INTERNAL_ERROR (Ck.internalError __FILE__ __LINE__)

#define CHECK(f) (Ck.f __FILE__ __LINE__)
#define BOUNDS_CHECK(f) (CHECK(f) Ck.Bounds)
#define UNSAFE_CHECK(f) (CHECK(f) Ck.Unsafe)
#define INTERNAL_CHECK(f) (CHECK(f) Ck.Internal)


