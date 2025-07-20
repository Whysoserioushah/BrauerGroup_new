import Mathlib.Algebra.Algebra.Equiv

notation "Gal("K ", "F")" => Gal(K, F)

namespace AlgEquiv
variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp] lemma apply_inv_self (e : A ≃ₐ[R] A) (x : A) : e (e⁻¹ x) = x := e.toEquiv.apply_symm_apply _
@[simp] lemma inv_apply_self (e : A ≃ₐ[R] A) (x : A) : e⁻¹ (e x) = x := e.toEquiv.symm_apply_apply _

end AlgEquiv
