import Coxeter.Basic
import Coxeter.Bruhat
import Coxeter.Rpoly
import Coxeter.Length_reduced_word
import Coxeter.Wellfounded

import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Reverse
import Mathlib.Data.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Data.Polynomial.Laurent
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Ring.Defs

variable {G :(Type _)} [Group G] {S : (Set G)} [orderTwoGen S] [CoxeterSystem G S]
local notation :max "ℓ(" g ")" => (@length G  _ S _ g)
open Classical



def Hecke {G :(Type _)} [Group G] (S : (Set G)) [orderTwoGen S] [CoxeterSystem G S]:= G →₀  (LaurentPolynomial ℤ)
--DirectSum G (fun _ => LaurentPolynomial ℤ)
--def Hecke (G:Type _):= Π₀ (i:G), (fun _ => LaurentPolynomial ℤ) i

noncomputable instance Hecke.AddCommMonoid : AddCommMonoid (Hecke S):= Finsupp.addCommMonoid

noncomputable instance Hecke.Module : Module (LaurentPolynomial ℤ) (Hecke S):= Finsupp.module _ _

noncomputable instance Hecke.AddCommGroup : AddCommGroup (Hecke S) := Module.addCommMonoidToAddCommGroup (LaurentPolynomial ℤ)

noncomputable instance Hecke.Module.Free : Module.Free (LaurentPolynomial ℤ) (Hecke S):= Module.Free.finsupp _ _ _

--noncomputable instance Hecke.Sub : Sub (Hecke S) := DFinsupp.instSubDFinsuppToZeroToNegZeroClassToSubNegZeroMonoidToSubtractionMonoid
--Dfinsupp.funlike
instance Hecke.funLike : FunLike (Hecke S) G (fun _ => LaurentPolynomial ℤ):= Finsupp.funLike

noncomputable instance LaurentPolynomial.CommSemiring : CommSemiring (LaurentPolynomial ℤ):=
AddMonoidAlgebra.commSemiring

noncomputable def TT : G → Hecke S:= fun w => Finsupp.single w 1


noncomputable instance TT.Basis : Basis G (LaurentPolynomial ℤ) (Hecke S) := Finsupp.basisSingleOne

#check finsum_eq_sum
#check Basis.sum_repr
-- ∀ h:Hecke G, h = ∑ᶠ w, (h w) * TT w
@[simp]
noncomputable def repr_of_Hecke_respect_TT (h:Hecke S):= Finsupp.total G (Hecke S) (LaurentPolynomial ℤ) (TT) (Basis.repr (TT.Basis) h)



lemma repr_apply (h:Hecke S):  repr_of_Hecke_respect_TT h = finsum fun w => (h w) • TT w :=by {
  simp
  rw [ Finsupp.total_apply]
  sorry
}

--Ts *Tw = Ts*Ts*Tu= (q-1)Ts*Tu+qTu=(qSS1) Tw + qT(s*w) if s∈D_L w
noncomputable def q :=@LaurentPolynomial.T ℤ _ 1

local notation : max "q⁻¹" => @LaurentPolynomial.T ℤ _ (-1)

--DFinsupp.single w (q-1) + DFinsupp.single (s*w) q))
noncomputable def mulsw {G : Type*} [Group G] {S : Set G} [orderTwoGen S] [CoxeterSystem G S]
 (s:S) (w:G)  : Hecke S :=
  if s.val ∈ D_L w then
  ((q-1) • (TT w) + q • (TT (s*w)))
  else TT (s*w)

--Ts* ∑ᶠ w, h (w) * TT w = ∑ᶠ h w * Ts * T w
noncomputable def muls --{G : Type*} [Group G] {S : Set G} [orderTwoGen S] [CoxeterSystem G S]
  (s:S) (h:Hecke S) : Hecke S:=
    finsum (fun w:G =>  (h w) • (mulsw s w) )
--∑ᶠ (w :G), ((h w) • (mulsw s w):Hecke G)

noncomputable def mulws --{G : Type*} [Group G] {S : Set G} [orderTwoGen S] [CoxeterSystem G S]
 (w:G) (s:S) : Hecke S :=
  if s.val ∈ D_R w then
  ((q-1) • (TT w) + q • (TT (w*s)))
  else TT (w*s)

noncomputable def muls_right (h:Hecke S) (s:S)  : Hecke S:=
finsum (fun w:G =>  (h w) • (mulws w s) )


noncomputable def mulw.F (u :G) (F:(w:G) → llr w u → Hecke S → Hecke S) (v:Hecke S): Hecke S:=
if h:u =1 then v
  else(
    let s:= Classical.choice (nonemptyD_L u h)
    have :s.val ∈ S:= Set.mem_of_mem_of_subset s.2 (Set.inter_subset_right _ S)
    muls ⟨s,this⟩ (F (s.val*u) (@llr_of_mem_D_L G _ S _ u s ) v)
  )

noncomputable def mulw :G → Hecke S → Hecke S := @WellFounded.fix G (fun _ => Hecke S → Hecke S) llr well_founded_llr mulw.F

lemma finsupp_mulsw_of_finsupp_Hecke (x:Hecke S) :Set.Finite (Function.support (fun w => x w • mulsw s w)):=by{
  have : Function.support (fun w => x w • mulsw s w) ⊆ {i | (x i) ≠ 0}:=by{
      simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
      intro w
      apply Function.mt
      intro h
      rw [h]
      simp
    }
  exact Set.Finite.subset (Finsupp.finite_support x) this
}

lemma finsupp_mulws_of_finsupp_Hecke (x:Hecke S) :Set.Finite (Function.support (fun w => x w • mulws w s)):=by{
  have : Function.support (fun w => x w • mulws w s) ⊆ {i | (x i) ≠ 0}:=by{
      simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
      intro w
      apply Function.mt
      intro h
      rw [h]
      simp
    }
  exact Set.Finite.subset (Finsupp.finite_support x) this
}

lemma finsupp_mul_of_directsum  (a c: Hecke S): Function.support (fun w ↦ ↑(a w) • mulw w c) ⊆  {i | ↑(a i) ≠ 0} := by {
  simp only [ne_eq, Function.support_subset_iff, Set.mem_setOf_eq]
  intro x
  apply Function.mt
  intro h
  rw [h]
  simp
}

local notation : max "End_ε" => Module.End (LaurentPolynomial ℤ) (Hecke S)

noncomputable instance End_ε.Algebra : Algebra (LaurentPolynomial ℤ) End_ε :=
Module.End.instAlgebra (LaurentPolynomial ℤ) (LaurentPolynomial ℤ) (Hecke S)
#check End_ε

noncomputable def opl (s:S) : (Hecke S)→ (Hecke S) := fun h:(Hecke S) => muls s h

--noncomputable def opl1 (w:G) := DirectSum.toModule  (LaurentPolynomial ℤ) G (Hecke G) (fun w:G => (fun (Hecke G) w => mulw w ))

noncomputable def opr (s:S) : (Hecke S )→ (Hecke S) := fun h:(Hecke S) => muls_right h s
#check Set.Finite.subset
noncomputable def opl' (s:S): End_ε :=
{
  toFun:=opl s
  map_add':=by{
    intro x y
    simp[opl,muls]
    rw [←finsum_add_distrib (finsupp_mulsw_of_finsupp_Hecke x) (finsupp_mulsw_of_finsupp_Hecke y)]
    congr
    apply funext
    intro w
    rw [Finsupp.add_apply,add_smul]
  }
  map_smul':=by{
    intro r x
    simp[opl,muls]
    rw[smul_finsum' r _]
    apply finsum_congr
    intro g
    rw [Finsupp.smul_apply,smul_smul]
    simp only [smul_eq_mul]
    exact finsupp_mulsw_of_finsupp_Hecke x
  }
}

noncomputable def opr' (s:S): End_ε :={
  toFun:=opr s
  map_add':=by{
    intro x y
    simp[opr,muls_right]
    rw [←finsum_add_distrib (finsupp_mulws_of_finsupp_Hecke x) (finsupp_mulws_of_finsupp_Hecke y)]
    congr
    apply funext
    intro w
    rw [Finsupp.add_apply,add_smul]
  }
  map_smul':=by{
    intro r x
    simp[opr,muls_right]
    rw[smul_finsum' r _]
    apply finsum_congr
    intro g
    rw [Finsupp.smul_apply,smul_smul]
    simp only [smul_eq_mul]
    exact finsupp_mulws_of_finsupp_Hecke x
  }
}

lemma TT_muls_right_eq_mul_of_length_lt {s:S} (h:ℓ(w)<ℓ(w*s)):  opr' s (TT w)  = TT (w*s):=by{
  simp [opr',opr,muls_right]
  have :mulws w s = TT (w * s):=by{
    rw [mulws]
    have notsinD_R :¬ (s.1 ∈ D_R w):=sorry
    simp [notsinD_R]
  }
  calc
    ∑ᶠ (w_1 : G), (TT w) w_1 • mulws w_1 s = TT w w • mulws w s:=by{
      apply finsum_eq_single
      intro x hx
      rw [TT,Finsupp.single_eq_of_ne (Ne.symm hx)]
      simp
    }
    _ = _ :=by{
      rw [TT,Finsupp.single_eq_same,this]
      simp
      }
}

lemma opl_commute_opr : ∀ s t:S, opl' s ∘ opr' t = opr' t ∘ opl' s:=by{
  intro s t
  sorry
}

def generator_set :=  opl' '' (Set.univ :Set S)
def generator_set' :=  opr' '' (Set.univ :Set S)

noncomputable def subalg {G : Type u_1} [Group G] (S : Set G) [orderTwoGen S] [CoxeterSystem G S]
:= Algebra.adjoin (LaurentPolynomial ℤ) (@generator_set G _ S _ _)

#check (subalg S).one


@[simp]
noncomputable def alg_hom_aux : subalg S→ (Hecke S) := fun f => f.1 (TT 1)
--compiler IR check failed at 'alg_hom_aux._rarg', error: unknown declaration 'TT'

noncomputable def subalg' {G : Type u_1} [Group G] (S : Set G) [orderTwoGen S] [CoxeterSystem G S]
:= Algebra.adjoin (LaurentPolynomial ℤ) (@generator_set' G _ S _ _)

@[simp]
noncomputable def alg_hom_aux' : subalg' S→ (Hecke S) := fun f => f.1 (TT 1)

noncomputable instance subalg.Algebra: Algebra (LaurentPolynomial ℤ) (subalg S) := Subalgebra.algebra (subalg S)
noncomputable instance subalg'.Algebra: Algebra (LaurentPolynomial ℤ) (subalg' S) := Subalgebra.algebra (subalg' S)

lemma subalg_commute_subalg' (f:subalg S) (g:subalg' S): f.1 ∘ g.1 = g.1 ∘ f.1:=sorry

noncomputable instance alg_hom_aux.IsLinearMap : IsLinearMap (LaurentPolynomial ℤ) (alg_hom_aux: subalg S → Hecke S) where
map_add:=by{
  intro x y
  simp [alg_hom_aux]
}
map_smul:=by {
  intro c x
  simp [alg_hom_aux]
}
noncomputable instance alg_hom_aux'.IsLinearMap : IsLinearMap (LaurentPolynomial ℤ) (alg_hom_aux': subalg' S → Hecke S) where
map_add:=by{
  intro x y
  simp [alg_hom_aux]
  --simp [alg_hom_aux']??????
}
map_smul:=by {
  intro c x
  simp [alg_hom_aux]
}

lemma TT_subset_image_of_alg_hom_aux_aux : ∀ l ,∀ w:G , l = ℓ(w) →∃ f:subalg' S, TT w = alg_hom_aux' f:= by{
  intro l w h
  induction' l with n hn
  {
    have := eq_one_of_length_eq_zero w (eq_comm.1 h)
    rw [this]
    use 1
    simp [alg_hom_aux']}
  {
    have hw:w≠1:=sorry
    let s:= Classical.choice (nonemptyD_R w hw)
    have :s.val ∈ S:= Set.mem_of_mem_of_subset s.2 (Set.inter_subset_right _ S)
    have h1:=length_mul_of_mem_D_R w hw s.2

  }
}

lemma alg_hom_aux_surjective: Function.Surjective (@alg_hom_aux G _ S _ _) := by {
  sorry
}

lemma alg_hom_aux'_surjective: Function.Surjective (@alg_hom_aux' G _ S _ _) := by {
  sorry
}
lemma alg_hom_injective_aux (f: subalg S) (h: alg_hom_aux f = 0) : f = 0 := by {
  simp at h
  have : ∀ w:G, f.1 (TT w) = 0:=by{
    intro w
    by_cases h1:w=1
    {rw[h1,h]}
    {
      have h1: ∀ g:subalg' S, g.1 (f.1 (TT 1)) = 0:=by{
        rw[h]
        intro g
        rw[map_zero]}
      have h2: ∀ g:subalg' S, f.1 (g.1 (TT 1)) = 0:=by{
        intro g
        rw [←@Function.comp_apply _ _ _ f.1,subalg_commute_subalg']
        exact h1 g
      }
      have :=@alg_hom_aux'_surjective G _ S _ _ (TT w)
      simp [alg_hom_aux'] at this
      rcases this with ⟨g,⟨hg1,hg2⟩⟩
      rw [←hg2]
      exact h2 ⟨g,hg1⟩
    }
  }
  sorry
}
#check injective_iff_map_eq_zero'
lemma alg_hom_aux_injective : Function.Injective  (alg_hom_aux :subalg S → Hecke S) := by {
  -- rw [Function.Injective]
  -- intro a1 a2 h
  -- sorry
  sorry
}


lemma alg_hom_aux_bijective : Function.Bijective (@alg_hom_aux G _ S _ _) := ⟨alg_hom_aux_injective, alg_hom_aux_surjective⟩

noncomputable def alg_hom {G :(Type _)} [Group G] (S : (Set G)) [orderTwoGen S] [CoxeterSystem G S]:LinearEquiv (@RingHom.id (LaurentPolynomial ℤ) _)  (subalg S) (Hecke S) where
  toFun:= alg_hom_aux
  map_add' := by simp
  map_smul' := by simp
  invFun := Function.surjInv alg_hom_aux_surjective
  left_inv := Function.leftInverse_surjInv alg_hom_aux_bijective
  right_inv := Function.rightInverse_surjInv alg_hom_aux_surjective

#check (@alg_hom G _ S _ _).invFun
#check (subalg S).1

lemma alg_hom_id : alg_hom S 1 = TT 1 :=by{simp[alg_hom]}
lemma subalg.id_eq :(alg_hom S).invFun (TT 1) = 1:=by{
  rw [←alg_hom_id]
  simp
}

noncomputable def HeckeMul : Hecke S → Hecke S → Hecke S := fun x =>(fun y => (alg_hom S).toFun ((alg_hom S).invFun x * (alg_hom S).invFun y))

lemma Hecke.mul_zero : ∀ (a : Hecke S), HeckeMul a 0 = 0 := by{
  intro a
  simp[HeckeMul]
}

lemma Hecke.zero_mul : ∀ (a : Hecke S),  HeckeMul 0 a = 0 := by{
  intro a
  simp[HeckeMul]
}

lemma Hecke.mul_assoc :∀ (a b c : Hecke S), HeckeMul (HeckeMul a b) c = HeckeMul a (HeckeMul b c):=by{
  intro a b c
  simp only [HeckeMul]
  sorry
}

lemma Hecke.one_mul : ∀ (a : Hecke S), HeckeMul (TT 1) a = a := by{
  intro a
  simp[HeckeMul]
  rw [←LinearEquiv.invFun_eq_symm,@subalg.id_eq G _ S _]
  simp
}

lemma Hecke.mul_one : ∀ (a : Hecke S), HeckeMul a (TT 1) = a := by{
  intro a
  simp[HeckeMul]
  rw [←LinearEquiv.invFun_eq_symm,@subalg.id_eq G _ S _]
  simp
}

#check DirectSum.add_apply


lemma Hecke.left_distrib : ∀ (a b c : Hecke S), HeckeMul a (b + c) = HeckeMul a b + HeckeMul a c := by{
  intro a b c
  simp[HeckeMul]
  rw [NonUnitalNonAssocSemiring.left_distrib]
  congr
}

lemma Hecke.right_distrib : ∀ (a b c : Hecke S),  HeckeMul (a + b)  c =  HeckeMul a c + HeckeMul b c :=by{
  intro a b c
  simp[HeckeMul]
  rw [NonUnitalNonAssocSemiring.right_distrib]
  congr
}


noncomputable instance Hecke.Semiring : Semiring (Hecke S) where
  add:= AddCommMonoid.add
  add_assoc:= AddCommMonoid.add_assoc
  zero:=0
  zero_add:=AddCommMonoid.zero_add
  add_zero:=AddCommMonoid.add_zero
  add_comm:=AddCommMonoid.add_comm
  nsmul:= AddCommMonoid.nsmul
  nsmul_zero:=AddCommMonoid.nsmul_zero
  nsmul_succ:=AddCommMonoid.nsmul_succ
  mul:=HeckeMul
  mul_zero:= Hecke.mul_zero
  zero_mul:= Hecke.zero_mul
  left_distrib:= Hecke.left_distrib
  right_distrib:= Hecke.right_distrib
  mul_assoc:=by{
    intro a b c
    rw [Semiring.mul]
  }
  one:=TT 1
  one_mul:=Hecke.one_mul
  mul_one:=Hecke.mul_one

lemma Hecke.smul_assoc : ∀ (r : LaurentPolynomial ℤ) (x y : Hecke S), HeckeMul (r • x) y = r • (HeckeMul x y):=by{
  intro r x y
  simp [HeckeMul]
}

lemma Hecke.smul_comm : ∀ (r : LaurentPolynomial ℤ) (x y : Hecke S), HeckeMul x (r • y) = r • (HeckeMul x y):=by{
  intro r x y
  simp [HeckeMul]
}

noncomputable instance Hecke.algebra : Algebra (LaurentPolynomial ℤ) (Hecke S):=
Algebra.ofModule (Hecke.smul_assoc) (Hecke.smul_comm)

--define (TT s)⁻¹
noncomputable def Hecke_inv_s (s:S) := q⁻¹ • (TT s.val) - (1-q⁻¹) • (TT 1)

noncomputable def Hecke_invG.F (u:G) (F: (w:G) → llr w u → Hecke S): Hecke S:= if h:u=1 then TT 1
else (
   let s:= Classical.choice (nonemptyD_L u h)
   HeckeMul (F (s*u) (@llr_of_mem_D_L G _ S _ u s)) (Hecke_inv_s s)
  )


noncomputable def Hecke_invG : G → Hecke S := @WellFounded.fix G (fun _ => Hecke S) llr well_founded_llr Hecke_invG.F

lemma Hecke_left_invG (u:G): (Hecke_invG u) * TT u  = 1 := by{sorry}

lemma Hecke_right_invG (u:G): TT u * (Hecke_invG u) = 1 :=by{
  rw [Hecke_invG]
  sorry
  }

def length_le_set (w:G) := {x:G| ℓ(x) ≤ ℓ(w)}

variable {R:@Rpoly G _ S _}

theorem Hecke_inverseG (w:G) : (Hecke_invG w⁻¹) = ((-1)^ℓ(w) * (q⁻¹)^ℓ(w)) • finsum (fun (x: length_le_set w) => (Polynomial.toLaurent ((-1)^ℓ(x)*(R.R x w))) • TT x.val):=sorry



section involution

noncomputable def iot_A : LaurentPolynomial ℤ →  LaurentPolynomial ℤ := LaurentPolynomial.invert

noncomputable def iot_T : G → Hecke S := fun w => Hecke_invG w

noncomputable def iot :Hecke S → Hecke S := fun h => finsum (fun x:G =>iot_A (h x) • TT x)

lemma iot_mul (x y :Hecke S) : iot (x*y) = iot x * iot y:= sorry

noncomputable instance iot.AlgHom : AlgHom (LaurentPolynomial ℤ) (Hecke S) (Hecke S) where
toFun:=iot
map_one':=sorry
map_mul':=iot_mul
map_zero':=sorry
map_add':=sorry
commutes':=sorry


end involution
