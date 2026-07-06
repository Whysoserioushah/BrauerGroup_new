module

public import BrauerGroup.MatrixCenterEquiv
public import BrauerGroup.TwoSidedIdeal
public import Mathlib.Algebra.Azumaya.Basic
public import Mathlib.Algebra.Central.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

@[expose] public section

variable (A : Type*) [Ring A]

open Matrix MulOpposite

local notation "M[" ι ", " R "]" => Matrix ι ι R

section simple_ring

open MulOpposite

variable (K D : Type*) [Field K] [IsSimpleRing A] [Algebra K A] [DivisionRing D]

-- /--
-- Division rings are a simple ring
-- -/
-- instance : IsSimpleOrder (TwoSidedIdeal D) where
--   eq_bot_or_eq_top r := by
--     obtain h | h := _root_.forall_or_exists_not (fun x ↦ x ∈ r ↔ x = 0)
--     · left
--       exact SetLike.ext fun x ↦ (h x).trans (by rfl)
--     · right
--       obtain ⟨x, hx⟩ := h
--       refine SetLike.ext fun y ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
--       have hx' : x ≠ 0 := by rintro rfl; simp [r.zero_mem] at hx
--       rw [show y = y * x * x⁻¹ by field_simp]
--       refine r.mul_mem_right _ _ <| r.mul_mem_left _ _ (by tauto)

instance op_simple : IsSimpleRing Aᵐᵒᵖ :=
  ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

/--
The canonical map from `Aᵒᵖ` to `Hom(A, A)`
-/
@[simps]
def mopToEnd : Aᵐᵒᵖ →+* Module.End A A where
  toFun a :=
    { toFun := fun x ↦ x * a.unop
      map_add' := by simp [add_mul]
      map_smul' := by simp [mul_assoc] }
  map_zero' := by aesop
  map_one' := by aesop
  map_add' := by aesop
  map_mul' := by aesop

/--
For any ring `D`, `Mₙ(D) ≅ Mₙ(D)ᵒᵖ`.
-/
@[simps]
def matrixEquivMatrixMop (n : ℕ) (D : Type*) [Ring D] :
    Matrix (Fin n) (Fin n) Dᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ where
  toFun M := MulOpposite.op (M.transpose.map (fun d => MulOpposite.unop d))
  invFun M := (MulOpposite.unop M).transpose.map (fun d => MulOpposite.op d)
  left_inv a := by aesop
  right_inv a := by aesop
  map_mul' x y := unop_injective <| by ext; simp [transpose_map, transpose_apply, mul_apply]
  map_add' x y := by aesop

end simple_ring

universe u v w
section central_simple

variable (K : Type u) (B : Type v) [Field K] [Ring B] [Algebra K B] [FiniteDimensional K B]

lemma Matrix.mem_center_iff' (K R : Type*) [Field K] [Ring R] [Algebra K R] (n : ℕ) (M) :
    M ∈ Subalgebra.center K M[Fin n, R] ↔
    ∃ α : (Subalgebra.center K R), M = α • 1 :=
  Matrix.mem_center_iff R n M

theorem RingEquiv.mem_center_iff {R1 R2 : Type*} [Ring R1] [Ring R2] (e : R1 ≃+* R2) :
    ∀ x, x ∈ Subring.center R1 ↔ e x ∈ Subring.center R2 := fun x ↦ by
  simpa only [Subring.mem_center_iff] using
    ⟨fun h r => e.symm.injective <| by simp [h], fun h r => e.injective <| by simpa using h (e r)⟩

variable {B} in
/--
For a `K`-algebra B, there is a map from `I : Ideal B` to `End(I)ᵒᵖ` defined by `k ↦ x ↦ k • x`.
-/
@[simps]
def algebraMapEndIdealMop (I : Ideal B) : K →+* (Module.End B I)ᵐᵒᵖ where
  toFun k := .op {
    toFun x := k • x
    map_add' := fun x y => by simp
    map_smul' := fun k' x => by ext; simp
  }
  map_one' := unop_injective <| by ext; simp
  map_mul' _ _ := unop_injective <| by ext; simp [SemigroupAction.mul_smul]
  map_zero' := unop_injective <| by ext; simp
  map_add' _ _ := unop_injective <| by ext; simp [add_smul]

instance (I : Ideal B) : Algebra K (Module.End B I)ᵐᵒᵖ where
  algebraMap := algebraMapEndIdealMop K I
  commutes' := fun r ⟨x⟩ => MulOpposite.unop_injective <| DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext <| show (x (r • ⟨i, hi⟩)).1 = r • (x ⟨i, hi⟩).1 by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) using 1 <;> aesop
  smul k x := .op <| (algebraMapEndIdealMop K I k).unop * x.unop
  smul_def' := fun r ⟨x⟩ => MulOpposite.unop_injective <| DFunLike.ext _ _ fun ⟨i, hi⟩ =>
    Subtype.ext <| by
      convert Subtype.ext_iff.mp (x.map_smul (algebraMap K B r) ⟨i, hi⟩) |>.symm using 1 <;> aesop

omit [FiniteDimensional K B] in
lemma algebraEndIdealMop.algebraMap_eq (I : Ideal B) :
    algebraMap K (Module.End B I)ᵐᵒᵖ = algebraMapEndIdealMop K I := rfl

lemma Wedderburn_Artin_algebra_version' (R : Type u) (A : Type v) [CommRing R] [Ring A]
    [sim : IsSimpleRing A] [Algebra R A] [hA : IsArtinianRing A] :
    ∃ n ≠ 0, ∃ (S : Type v) (_ : DivisionRing S) (_ : Algebra R S),
    Nonempty (A ≃ₐ[R] (M[Fin n, S])) := by
  obtain ⟨n, hn, S, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing R A
  exact ⟨n, hn.out, S, inferInstance, inferInstance, ⟨e⟩⟩

lemma Wedderburn_Artin_algebra_version
    [sim : IsSimpleRing B] :
    ∃ n ≠ 0, ∃ (S : Type v) (_ : DivisionRing S) (_ : Algebra K S),
      Nonempty (B ≃ₐ[K] (M[Fin n, S])) := by
  classical
  have hB : IsArtinianRing B := .of_finite K B
  exact Wedderburn_Artin_algebra_version' K B

omit [FiniteDimensional K B] in
theorem is_central_of_wdb [hctr : Algebra.IsCentral K B]
    (n : ℕ) (S : Type*) (hn : n ≠ 0) [h : DivisionRing S]
    [Algebra K S] (Wdb : B ≃ₐ[K] M[Fin n, S]) :
    Algebra.IsCentral K S := by
  have : NeZero n := ⟨hn⟩
  constructor
  intro x hx
  have hx' : (Matrix.diagonal fun _ ↦ x) ∈ Subalgebra.center K M[Fin n, S] := by
    refine Matrix.mem_center_iff' _ _ _ _ |>.2 ⟨⟨x, hx⟩, ?_⟩
    ext
    simp only [diagonal, of_apply]
    split_ifs
    · simp_all only [Matrix.smul_apply, one_apply_eq]
      change _ = x • (1 : S)
      simp only [smul_eq_mul, mul_one]
    · simp_all
  have hx'' : Wdb.symm (Matrix.diagonal fun _ ↦ x) ∈ Subalgebra.center K B := by
    rw [Subalgebra.mem_center_iff] at hx' ⊢
    exact fun b ↦ Wdb.injective <| by simpa using hx' (Wdb b)
  obtain ⟨s, (hs : algebraMap _ _ s = _)⟩ := hctr.out hx''
  exact ⟨s, show algebraMap _ _ _ = _ by
    simpa [Matrix.algebraMap_eq_diagonal] using Matrix.ext_iff.2 congr(Wdb $hs) 0 0⟩

theorem is_fin_dim_of_wdb {n : ℕ} (hn : n ≠ 0) (S : Type*) [h : DivisionRing S] [Algebra K S]
    (Wdb : B ≃ₐ[K] M[Fin n, S]) : FiniteDimensional K S := by
  classical
  have : NeZero n := ⟨hn⟩
  have := FiniteDimensional.of_injective Wdb.symm.toLinearEquiv.toLinearMap Wdb.symm.injective
  exact Module.Finite.of_injective
      ({
        toFun s := Matrix.diagonal (fun _ => s)
        map_add' := by
          intros; ext i j; by_cases i = j  <;> aesop
        map_smul' := by intros; ext i j; by_cases i = j  <;> aesop
      } : S →ₗ[K] Matrix (Fin n) (Fin n) S) fun x y h => Matrix.ext_iff.2 h 0 0

theorem simple_eq_matrix_algClosed [IsAlgClosed K] [IsSimpleRing B] :
    ∃ n ≠ 0, Nonempty (B ≃ₐ[K] M[Fin n, K]) := by
  rcases Wedderburn_Artin_algebra_version K B with ⟨n, hn, S, ins1, ins2, ⟨e⟩⟩
  have := is_fin_dim_of_wdb K B hn S e
  exact ⟨n, hn, ⟨e.trans <| .mapMatrix <| .symm <|
    .ofBijective (Algebra.ofId _ _) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

end central_simple
