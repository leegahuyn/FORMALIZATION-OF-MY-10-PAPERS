import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Roots of unity as locally constant sections

Over an algebraically closed field where the degree is invertible, an affine
section of the root-of-unity kernel determines a locally constant root label
on the prime spectrum. This treatment allows disconnected affine objects.
-/

namespace ManuscriptAudit.KummerRootLabels

open scoped BigOperators Topology

noncomputable section

variable {A B K : Type*} [CommRing A] [CommRing B] [Field K]

/-- The image of a unit root of unity under a ring homomorphism. -/
def mapRoots (d : ℕ) (f : A →+* B) : rootsOfUnity d A →* rootsOfUnity d B :=
  MonoidHom.codRestrict ((Units.map f.toMonoidHom).comp (rootsOfUnity d A).subtype)
    (rootsOfUnity d B) fun a => map_rootsOfUnity (Units.map f.toMonoidHom) d
      ⟨a.1, a.2, rfl⟩

private abbrev rootValue {R : Type*} [CommRing R] {d : ℕ} (a : rootsOfUnity d R) : R :=
  ((a : Rˣ) : R)

variable [IsAlgClosed K] [Algebra K A] {d : ℕ} [NeZero d] [NeZero (d : K)]

private abbrev coefficientResidue (P : PrimeSpectrum A) : K →+* A ⧸ P.asIdeal :=
  (Ideal.Quotient.mk P.asIdeal).comp (algebraMap K A)

private theorem coefficientResidue_injective (P : PrimeSpectrum A) :
    Function.Injective (coefficientResidue (K := K) P) := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact RingHom.injective _

private theorem primitiveRoots_nonempty : (primitiveRoots d K).Nonempty := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K d
  exact ⟨ζ, (mem_primitiveRoots (NeZero.pos d)).mpr hζ⟩

private def rootTagHom (P : PrimeSpectrum A) : rootsOfUnity d A →* rootsOfUnity d K := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact (rootsOfUnityEquivOfPrimitiveRoots (coefficientResidue_injective (K := K) P)
    (primitiveRoots_nonempty (K := K) (d := d))).symm.toMonoidHom.comp
      (mapRoots d (Ideal.Quotient.mk P.asIdeal))

private def rootTag (a : rootsOfUnity d A) (P : PrimeSpectrum A) : rootsOfUnity d K :=
  rootTagHom P a

private theorem rootTag_residue (a : rootsOfUnity d A) (P : PrimeSpectrum A) :
    coefficientResidue P (rootValue (rootTag (K := K) a P)) =
      Ideal.Quotient.mk P.asIdeal (rootValue a) := by
  letI : IsDomain (A ⧸ P.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    (coefficientResidue_injective (K := K) P)
    (primitiveRoots_nonempty (K := K) (d := d))
    (mapRoots d (Ideal.Quotient.mk P.asIdeal) a)

private theorem rootTag_eq_iff (a : rootsOfUnity d A) (P : PrimeSpectrum A)
    (ζ : rootsOfUnity d K) :
    rootTag a P = ζ ↔ rootValue a - algebraMap K A (rootValue ζ) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq]
  constructor
  · intro h
    rw [← h]
    exact (rootTag_residue (K := K) a P).symm
  · intro h
    apply Subtype.ext
    apply Units.ext
    apply coefficientResidue_injective (K := K) P
    exact (rootTag_residue (K := K) a P).trans h

private theorem rootTag_fiber (a : rootsOfUnity d A) (ζ : rootsOfUnity d K) :
    rootTag a ⁻¹' {ζ} = PrimeSpectrum.zeroLocus {rootValue a - algebraMap K A (rootValue ζ)} := by
  ext P
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff, SetLike.mem_coe] using rootTag_eq_iff a P ζ

private theorem isLocallyConstant_rootTag (a : rootsOfUnity d A) :
    IsLocallyConstant (rootTag (K := K) a) := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro ζ
  have hcompl : (rootTag (K := K) a ⁻¹' {ζ})ᶜ =
      ⋃ η : {η : rootsOfUnity d K // η ≠ ζ}, rootTag a ⁻¹' {η.1} := by
    ext P
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨⟨rootTag a P, h⟩, rfl⟩
    · rintro ⟨η, h⟩ heq
      exact η.2 (h.symm.trans heq)
  rw [← isClosed_compl_iff, hcompl]
  apply isClosed_iUnion_of_finite
  intro η
  rw [rootTag_fiber]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- A root of unity determines its coefficient-root label at every prime.
The label is locally constant and multiplicative in the input. -/
def locallyConstantRootTag :
    rootsOfUnity d A →* LocallyConstant (PrimeSpectrum A) (rootsOfUnity d K) where
  toFun a := ⟨rootTag a, isLocallyConstant_rootTag a⟩
  map_one' := LocallyConstant.ext fun P => (rootTagHom P).map_one
  map_mul' a b := LocallyConstant.ext fun P => (rootTagHom P).map_mul a b

/-- Each coefficient-root fiber is the clopen defined by an idempotent. -/
theorem locallyConstantRootTag_idempotent (a : rootsOfUnity d A) (ζ : rootsOfUnity d K) :
    ∃ e : A, IsIdempotentElem e ∧
      {P | locallyConstantRootTag a P = ζ} = PrimeSpectrum.basicOpen e :=
  PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    ((isLocallyConstant_rootTag a).isClopen_fiber ζ)

/-- The locally constant label is compatible with change of affine object. -/
theorem locallyConstantRootTag_natural [Algebra K B] (f : A →ₐ[K] B)
    (a : rootsOfUnity d A) (P : PrimeSpectrum B) :
    locallyConstantRootTag (K := K) (mapRoots d f.toRingHom a) P =
      locallyConstantRootTag (K := K) a (PrimeSpectrum.comap f.toRingHom P) := by
  change rootTag (K := K) (mapRoots d f.toRingHom a) P =
    rootTag (K := K) a (PrimeSpectrum.comap f.toRingHom P)
  apply (rootTag_eq_iff _ _ _).mpr
  let Q := PrimeSpectrum.comap f.toRingHom P
  have h := (rootTag_eq_iff a Q (rootTag (K := K) a Q)).mp rfl
  change f (rootValue a - algebraMap K A (rootValue (rootTag (K := K) a Q))) ∈ P.asIdeal at h
  rw [map_sub, f.commutes] at h
  exact h

/-- A coefficient root has its own label at all primes of the algebra. -/
theorem locallyConstantRootTag_coeff (ζ : rootsOfUnity d K) (P : PrimeSpectrum A) :
    locallyConstantRootTag (mapRoots d (algebraMap K A) ζ) P = ζ := by
  change rootTag (mapRoots d (algebraMap K A) ζ) P = ζ
  apply (rootTag_eq_iff _ _ _).mpr
  change algebraMap K A (rootValue ζ) - algebraMap K A (rootValue ζ) ∈ P.asIdeal
  rw [sub_self]
  exact P.asIdeal.zero_mem

/-- The labels determine the original root of unity. For roots with the same
labels, the geometric sum of their quotient is a unit since it is congruent
to the degree modulo the nilradical. -/
theorem locallyConstantRootTag_injective :
    Function.Injective (locallyConstantRootTag (K := K) (A := A) (d := d)) := by
  intro a b hab
  have hdiv : locallyConstantRootTag (K := K) (a / b) = 1 := by
    rw [map_div, hab]
    apply LocallyConstant.ext
    intro P
    let z := locallyConstantRootTag (K := K) b P
    change z / z = 1
    exact div_eq_one.mpr rfl
  let t := rootValue (a / b)
  have htres (P : PrimeSpectrum A) : Ideal.Quotient.mk P.asIdeal t = 1 := by
    have hlabel : rootTag (K := K) (a / b) P = 1 := DFunLike.congr_fun hdiv P
    have h := (rootTag_residue (K := K) (a / b) P).symm
    rw [hlabel] at h
    simpa [t, rootValue] using h
  let s : A := ∑ i ∈ Finset.range d, t ^ i
  have hnil : IsNilpotent (s - (d : A)) := by
    apply nilpotent_iff_mem_prime.mpr
    intro I hI
    let P : PrimeSpectrum A := ⟨I, hI⟩
    let q := Ideal.Quotient.mk P.asIdeal
    apply Ideal.Quotient.eq.mp
    change q (∑ i ∈ Finset.range d, t ^ i) = q (d : A)
    have hqt : q t = 1 := htres P
    rw [map_sum, map_natCast]
    simp only [map_pow, hqt, one_pow, Finset.sum_const, Finset.card_range, nsmul_one]
  have hd : IsUnit (d : A) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K A)
  have hs : IsUnit s := by
    have h := hnil.isUnit_add_right_of_commute hd (show Commute (s - (d : A)) (d : A) from mul_comm _ _)
    simpa only [sub_add_cancel] using h
  have ht : t ^ d = 1 := (mem_rootsOfUnity' d ((a / b : rootsOfUnity d A) : Aˣ)).mp (a / b).prop
  have hgeom : (t - 1) * s = 0 := by
    simpa only [s, ht, sub_self] using mul_geom_sum t d
  obtain ⟨u, hu⟩ := hs
  have hsub : t - 1 = 0 := calc
    t - 1 = ((t - 1) * s) * ↑u⁻¹ := by rw [mul_assoc, ← hu, Units.mul_inv, mul_one]
    _ = 0 := by rw [hgeom, zero_mul]
  apply div_eq_one.mp
  apply rootsOfUnity.coe_injective
  exact sub_eq_zero.mp hsub

/-- Each locally constant coefficient-root label comes from a root of unity
on any algebra. Clopen fibers supply its orthogonal idempotent coordinates. -/
theorem locallyConstantRootTag_surjective :
    Function.Surjective (locallyConstantRootTag (K := K) (A := A) (d := d)) := by
  classical
  intro w
  letI := Fintype.ofFinite (rootsOfUnity d K)
  choose e he hFiber using fun ζ : rootsOfUnity d K =>
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
      (w.isLocallyConstant.isClopen_fiber ζ)
  have horth (ξ η : rootsOfUnity d K) (hne : ξ ≠ η) : e ξ * e η = 0 := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem
      (show IsIdempotentElem (e ξ * e η) from (he ξ).mul (he η)) IsIdempotentElem.zero
    rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_zero]
    apply bot_unique
    intro P hP
    have hξ : P ∈ (PrimeSpectrum.basicOpen (e ξ) : Set (PrimeSpectrum A)) := hP.1
    have hη : P ∈ (PrimeSpectrum.basicOpen (e η) : Set (PrimeSpectrum A)) := hP.2
    rw [← hFiber ξ] at hξ
    rw [← hFiber η] at hη
    exact (hne (hξ.symm.trans hη)).elim
  have hWeighted (ξ : rootsOfUnity d K) (g : rootsOfUnity d K → A) :
      e ξ * (∑ η, e η * g η) = e ξ * g ξ := by
    rw [Finset.mul_sum]
    refine (Finset.sum_eq_single ξ ?_ ?_).trans ?_
    · intro η _ hη
      rw [← mul_assoc, horth ξ η hη.symm, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
    · rw [← mul_assoc, he ξ]
  have hqWeighted (g : rootsOfUnity d K → A) (P : PrimeSpectrum A) :
      Ideal.Quotient.mk P.asIdeal (∑ ζ, e ζ * g ζ) =
        Ideal.Quotient.mk P.asIdeal (g (w P)) := by
    letI : IsDomain (A ⧸ P.asIdeal) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
    let q := Ideal.Quotient.mk P.asIdeal
    have heone : q (e (w P)) = 1 := by
      have hn : e (w P) ∉ P.asIdeal := by
        apply (PrimeSpectrum.mem_basicOpen _ _).mp
        change P ∈ (PrimeSpectrum.basicOpen (e (w P)) : Set (PrimeSpectrum A))
        rw [← hFiber]
        rfl
      rcases (IsIdempotentElem.iff_eq_zero_or_one).mp ((he (w P)).map q) with hzero | hone
      · exact (hn (Ideal.Quotient.eq_zero_iff_mem.mp hzero)).elim
      · exact hone
    have hezero (ζ : rootsOfUnity d K) (hζ : ζ ≠ w P) : q (e ζ) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      by_contra hn
      have hP := (PrimeSpectrum.mem_basicOpen (e ζ) P).mpr hn
      change P ∈ (PrimeSpectrum.basicOpen (e ζ) : Set (PrimeSpectrum A)) at hP
      rw [← hFiber] at hP
      exact hζ hP.symm
    change q (∑ ζ : rootsOfUnity d K, e ζ * g ζ) = q (g (w P))
    rw [map_sum]
    refine (Finset.sum_eq_single (w P) ?_ ?_).trans ?_
    · intro ζ _ hζ
      rw [map_mul, hezero ζ hζ, zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
    · rw [map_mul, heone, one_mul]
  have hsumIdem : IsIdempotentElem (∑ ζ, e ζ) := by
    change (∑ ζ, e ζ) * (∑ ζ, e ζ) = ∑ ζ, e ζ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ζ _
    simpa only [mul_one] using hWeighted ζ (fun _ => 1)
  have hsum : (∑ ζ, e ζ) = 1 := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem hsumIdem IsIdempotentElem.one
    rw [PrimeSpectrum.basicOpen_one]
    apply top_unique
    intro P _
    apply (PrimeSpectrum.mem_basicOpen _ _).mpr
    intro hmem
    letI : IsDomain (A ⧸ P.asIdeal) :=
      (Ideal.Quotient.isDomain_iff_prime _).mpr P.isPrime
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hone : Ideal.Quotient.mk P.asIdeal (∑ ζ, e ζ) = 1 := by
      simpa only [mul_one, map_one] using hqWeighted (fun _ => 1) P
    exact zero_ne_one (hzero.symm.trans hone)
  let c : rootsOfUnity d K → A := fun ζ => algebraMap K A (rootValue ζ)
  let z : A := ∑ ζ, e ζ * c ζ
  have hpower (ζ : rootsOfUnity d K) (n : ℕ) : e ζ * z ^ n = e ζ * c ζ ^ n := by
    induction n with
    | zero => simp only [pow_zero, mul_one]
    | succ n ih =>
      simp only [pow_succ, ← mul_assoc, ih]
      calc
        e ζ * c ζ ^ n * z = c ζ ^ n * (e ζ * z) := by ac_rfl
        _ = c ζ ^ n * (e ζ * c ζ) := congrArg (fun y => c ζ ^ n * y) (hWeighted ζ c)
        _ = e ζ * c ζ ^ n * c ζ := by ac_rfl
  have hz : z ^ d = 1 := calc
    z ^ d = (∑ ζ, e ζ) * z ^ d := by rw [hsum, one_mul]
    _ = ∑ ζ, e ζ * z ^ d := Finset.sum_mul _ _ _
    _ = ∑ ζ, e ζ := by
      apply Finset.sum_congr rfl
      intro ζ _
      have hc : c ζ ^ d = 1 := by
        change (algebraMap K A (rootValue ζ)) ^ d = 1
        rw [← map_pow, (mem_rootsOfUnity' d (ζ : Kˣ)).mp ζ.prop, map_one]
      rw [hpower, hc, mul_one]
    _ = 1 := hsum
  refine ⟨rootsOfUnity.mkOfPowEq z hz, LocallyConstant.ext fun P => ?_⟩
  change rootTag (rootsOfUnity.mkOfPowEq z hz) P = w P
  apply (rootTag_eq_iff _ _ _).mpr
  exact Ideal.Quotient.eq.mp (hqWeighted c P)

/-- Roots of unity on an affine algebra are exactly the locally constant
maps from its prime spectrum to coefficient roots. -/
def locallyConstantRootsEquiv :
    rootsOfUnity d A ≃* LocallyConstant (PrimeSpectrum A) (rootsOfUnity d K) :=
  MulEquiv.ofBijective locallyConstantRootTag
    ⟨locallyConstantRootTag_injective, locallyConstantRootTag_surjective⟩

end

end ManuscriptAudit.KummerRootLabels

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_idempotent,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_natural,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_coeff,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_injective,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootTag_surjective,
      ``ManuscriptAudit.KummerRootLabels.locallyConstantRootsEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
