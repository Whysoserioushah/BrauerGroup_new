import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.TensorProduct.Basic

suppress_compilation

open scoped TensorProduct

variable (K F : Type*) [CommSemiring K] [CommSemiring F] [Algebra F K]
    (A : Type*) (n : Type*) [Ring A] [Algebra F A] [DecidableEq n] [Fintype n]

open Matrix

def toTensorMartrix_toFun_bilinear : K →ₗ[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) where
  toFun k := {
    toFun M := k • Algebra.TensorProduct.includeRight.mapMatrix M
    map_add' _ _ := by simp [← smul_add, map_add]
    map_smul' r M := by simpa using smul_comm _ _ _
  }
  map_add' k1 k2 := by ext; simp [add_smul]
  map_smul' r k := by ext; simp

@[simp]
lemma toTensorMartrix_toFun_bilinear_apply (k : K) (M : Matrix n n A) :
  toTensorMartrix_toFun_bilinear K F A n k M =
  k • Algebra.TensorProduct.includeRight.mapMatrix M := rfl

abbrev toTensorMatrix_toFun_Flinear : K ⊗[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) :=
  TensorProduct.lift <| toTensorMartrix_toFun_bilinear K F A n

abbrev toTensorMatrix_toFun_Klinear : K ⊗[F] Matrix n n A →ₗ[K] Matrix n n (K ⊗[F] A) :=
  {__ := toTensorMatrix_toFun_Flinear K F A n,
   map_smul' k tensor := by
    induction tensor with
    | zero => simp
    | tmul k0 M => simp [TensorProduct.smul_tmul', SemigroupAction.mul_smul]
    | add _ _ h1 h2 => simp_all}

abbrev toTensorMatrix : K ⊗[F] Matrix n n A →ₐ[K] Matrix n n (K ⊗[F] A) :=
  .ofLinearMap (toTensorMatrix_toFun_Klinear K F A n) (by simp [Algebra.TensorProduct.one_def])
    fun t1 t2 ↦ by
  induction t1 with
  | zero => simp
  | tmul x y =>
    induction t2 with
    | zero => simp
    | tmul x0 y0 =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_comm x x0, LinearMap.coe_mk,
          TensorProduct.lift.tmul', toTensorMartrix_toFun_bilinear_apply, AlgHom.mapMatrix_apply,
          SemigroupAction.mul_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
        rw [Matrix.map_mul]
    | add _ _ h1 h2 => simp_all [mul_add]
  | add _ _ h1 h2 => simp_all [add_mul]

open TensorProduct

def invFun_toFun_bilinear (i j : n) : K →ₗ[F] A →ₗ[F] K ⊗[F] Matrix n n A where
  toFun k := {
    toFun a := k ⊗ₜ single i j a
    map_add' _ _ := by simp [single_add, tmul_add]
    map_smul' _ _ := by simp [← smul_single]
  }
  map_add' _ _ := by ext; simp [add_tmul]
  map_smul' _ _ := by ext; simp [smul_tmul']

omit [Fintype n] in
@[simp]
lemma invFun_toFun_bilinear_apply (i j : n) (k : K) (a : A) :
  invFun_toFun_bilinear K F A n i j k a = k ⊗ₜ single i j a := rfl

abbrev invFun_toFun (i j : n) : K ⊗[F] A →ₗ[F] K ⊗[F] Matrix n n A :=
  TensorProduct.lift <| invFun_toFun_bilinear K F A n i j

abbrev invFun_Klinear (i j : n) : K ⊗[F] A →ₗ[K] K ⊗[F] Matrix n n A :=
  {__ := invFun_toFun K F A n i j,
   map_smul' k tensor := by
    induction tensor with
    | zero => simp
    | tmul k0 a => simp [smul_tmul']
    | add _ _ h1 h2 => simp_all}

abbrev invFun_linearMap : Matrix n n (K ⊗[F] A) →ₗ[K] K ⊗[F] Matrix n n A where
  toFun M := ∑ p : n × n, invFun_Klinear K F A n p.1 p.2 (M p.1 p.2)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

lemma left_inv (M : K ⊗[F] Matrix n n A) :
    invFun_linearMap K F A n (toTensorMatrix K F A n M) = M := by
  induction M with
  | zero => simp
  | tmul k M =>
    simp [← tmul_sum, smul_tmul', Fintype.sum_prod_type, ← matrix_eq_sum_single]
  | add koxa1 koxa2 h1 h2 => rw [map_add, map_add, h1, h2]

lemma right_inv (M : Matrix n n (K ⊗[F] A)) :
    toTensorMatrix K F A n (invFun_linearMap K F A n M) = M := by
  simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, AddHom.coe_mk, map_sum,
    AlgHom.ofLinearMap_apply, Fintype.sum_prod_type]
  conv_rhs => rw [matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  induction M p q with
  | zero => simp
  | tmul x y => simp [smul_tmul']
  | add _ _ h1 h2 => simp [single_add, h1, h2]

def equivTensor' : K ⊗[F] Matrix n n A ≃ Matrix n n (K ⊗[F] A) where
  toFun := toTensorMatrix K F A n
  invFun := invFun_linearMap K F A n
  left_inv := left_inv K F A n
  right_inv := right_inv K F A n

def matrixTensorEquivTensor : K ⊗[F] Matrix n n A ≃ₐ[K] Matrix n n (K ⊗[F] A) :=
  {toTensorMatrix K F A n, equivTensor' K F A n with}

@[simp]
lemma matrixTensorEquivTensor_apply (M : K ⊗[F] Matrix n n A) :
    matrixTensorEquivTensor K F A n M = toTensorMatrix K F A n M := rfl

@[simp]
lemma matrixTensorEquivTensor_symm_apply (M : Matrix n n (K ⊗[F] A)) :
    (matrixTensorEquivTensor K F A n).symm M = invFun_linearMap K F A n M := rfl
