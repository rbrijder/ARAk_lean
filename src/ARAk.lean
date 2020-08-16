import init.function
import data.set.finite

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

-- ARA result

inductive ARAe (rel att: Type) : Type
| relnm (R : rel) : ARAe
| union : ARAe → ARAe → ARAe
| proj (Y : set att) : ARAe → ARAe
| selection (Y : set att) : ARAe → ARAe
| rename (φ : att → att) : ARAe → ARAe -- TODO: move injective condition to here?
| join : ARAe → ARAe → ARAe

namespace ARAe

section ARA
parameters {rel att dom: Type}

--variables {att_compat: att → att → Prop} [equivalence att_compat]
def mut_compat (att_compat: att → att → Prop) (Y: set att) : Prop := ∀ x y ∈ Y, att_compat x y
--def compat_func (att_compat: att → att → Prop) (φ : att → att) : Prop := ∀ x ∈ att, att_compat x (φ x)

-- defines schema of an ARA expression
def ARAschema (e : ARAe rel att) (S : rel → set att) : set att :=
ARAe.rec_on e S -- = (λ R, S(R)) -- relnm
              (λ e1 e2 e1S e2S, e1S ∪ e2S) -- union
              (λ Y e1 e1S, e1S ∩ Y) -- proj
              (λ Y e1 e1S, e1S) -- selection
              (λ φ e1 e1S, set.image φ e1S) -- rename
              (λ e1 e2 e1S e2S, e1S ∪ e2S) -- join

-- def well typed
def ARA_well_typed (e : ARAe rel att) (S : rel → set att) (att_compat: att → att → Prop) : Prop :=
ARAe.rec_on e (λ R, true) -- relnm
              (λ e1 e2 e1W e2W, e1W ∧ e2W ∧ (ARAschema e1 S = ARAschema e2 S)) -- union
              (λ Y e1 e1W, e1W) -- proj
              (λ Y e1 e1W, e1W ∧ mut_compat att_compat Y) -- selection
              (λ φ e1 e1W, e1W ∧ function.injective φ) -- rename
              (λ e1 e2 e1W e2W, e1W ∧ e2W) -- join

-- def semantics
--variable Da: att → D -- let us instead assume for now that dom is finite and Da(A)=dom

variables (X X' : set att)
@[reducible] def tuple := X → dom -- [fintype X] 
variables (α : Type) [semiring α]

def relation (α : Type) := tuple X → α

def rel_one : relation X α := (λ t, 1)
def rel_union (r : relation X α) (r' : relation X' α) :
              relation (X ∪ X') α := (λ t, r(t ∘ set.inclusion (set.subset_union_left X X')) + 
                                          r'(t ∘ set.inclusion (set.subset_union_right X X'))) --(λ t, r t + r' t)
def rel_proj (r : relation X α) (Y : set att) (hfin : fintype (tuple X)) :
              relation (X ∩ Y) α := (λ t, finset.sum (set.finite.to_finset (set.finite.of_fintype -- use finsum
                                    {t' : tuple X | t = t' ∘ set.inclusion (set.inter_subset_left X Y)})) r)
def rel_selection (r : relation X α) (Y : set att) :
              relation X α := (λ t, if (∀ y1 y2 : (X ∩ Y), t (set.inclusion (set.inter_subset_left X Y) y1) = 
                                                     t (set.inclusion (set.inter_subset_left X Y) y2)) then r(t) else 0)
def rel_renaming (r : relation X α) (φ : att → att) :
              relation (φ '' X) α := (λ t, r(t ∘ (set.maps_to.restrict φ X (φ '' X) (set.maps_to_image φ X))))
def rel_join (r : relation X α) (r' : relation X' α) :
              relation (X ∪ X') α := (λ t, r(t ∘ set.inclusion (set.subset_union_left X X')) * 
                                          r'(t ∘ set.inclusion (set.subset_union_right X X')))

def db_instance (S : rel → set att) := Π (R : rel), relation (S R) α

-- replace everywhere set att by finset att ??
theorem fin_tuples (e : ARAe rel att) (S : rel → set att) (h : (∀ R : rel, set.finite (S R))) :
fintype (tuple (ARAschema e S)) := sorry

def ARA_semantics (e : ARAe rel att) (S : rel → set att) (h : (∀ R : rel, set.finite (S R))) (att_compat: att → att → Prop) 
                  (I : db_instance α S) : -- (h : ARA_well_typed e S att_compat) 
                  relation (ARAschema e S) α :=
ARAe.rec_on e (λ R, I R) -- relnm
              (λ e1 e2 e1W e2W, rel_union (ARAschema e1 S) (ARAschema e2 S) α e1W e2W) -- union
              (λ Y e1 e1W, rel_proj (ARAschema e1 S) α e1W Y (fin_tuples e1 S h)) -- proj
              (λ Y e1 e1W, rel_selection (ARAschema e1 S) α e1W Y) -- selection
              (λ φ e1 e1W, rel_renaming (ARAschema e1 S) α e1W φ) -- rename
              (λ e1 e2 e1W e2W, rel_join (ARAschema e1 S) (ARAschema e2 S) α e1W e2W) -- join

end ARA
end ARAe
