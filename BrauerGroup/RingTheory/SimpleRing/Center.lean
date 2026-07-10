module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.FieldTheory.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Field

/-!
# The center of a simple algebra

The center of a simple algebra `B` is a field (`IsSimpleRing.isField_center`), and `B` is an
algebra over it; when `B` is finite-dimensional over a base field, it is finite-dimensional
over its center as well. These instances let one treat a simple algebra as a central simple
algebra over its own center.
-/

@[expose] public section

namespace Subalgebra.center

variable (F B : Type*) [Field F] [Ring B] [Algebra F B]

instance : SMulCommClass (Subalgebra.center F B) B B where
  smul_comm x y z := by
    change x.1 * (y * z) = y * (x.1 * z)
    rw [← mul_assoc, ← Subalgebra.mem_center_iff.1 x.2 y, mul_assoc]

scoped instance : Algebra (Subalgebra.center F B) B :=
  fast_instance% inferInstanceAs <| Algebra (Subring.center B) B

end Subalgebra.center
