import BrauerGroup.Subfield.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace SubField
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] {L : SubField K A}

instance [FiniteDimensional K A] : FiniteDimensional K L := .finiteDimensional_subalgebra L.1

end SubField
