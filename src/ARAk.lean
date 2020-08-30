import init.function
import data.set.finite
import init.data.quot
import data.setoid.partition

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

------------------------ for mathlib? -------------------------------
namespace finset

universes u v

-- finset equivalent to set.maps_to_image. Similar to: set.maps_to_image f ↑s
theorem maps_to_image {α : Type u} {β : Type v} (f : α → β) (s : finset α) :
set.maps_to f ↑s ↑(finset.image f s) :=
begin
rw set.maps_to',
rw finset.coe_image,
end

end finset

namespace set

universes u v
def func_to_univ {α : Type u} {β : Type v} (f : α → β) : (@set.univ α) → (@set.univ β) :=
set.maps_to.restrict f set.univ set.univ (set.maps_to_univ f set.univ)

end set
---------------------------------------------------------------------

namespace ARA
section ARA
-- The goal is to prove the main ARA result

@[reducible] def mut_compat {att : Type} [setoid att] (Y : set att) : Prop := ∀ x y ∈ Y, x ≈ y
@[reducible] def compat_func {att : Type} [setoid att] {X Y : set att} (φ : X → Y) : Prop := ∀ x : X, (x : att) ≈ ((φ x) : att)

inductive ARAe (rel att : Type) [setoid att] : Type
| relnm (R : rel) : ARAe
| union : ARAe → ARAe → ARAe
| proj (Y : finset att) : ARAe → ARAe
| selection (Y : finset att) (hmutc : mut_compat (↑Y : set att)) : ARAe → ARAe
| rename (φ : att → att) (hinj : function.injective φ) (hc : compat_func (set.func_to_univ φ)) : ARAe → ARAe
| join : ARAe → ARAe → ARAe

parameters {rel att dom : Type} [setoid att]

-- defines schema of an ARA expression
def ARAschema (e : ARAe rel att) (S : rel → finset att) : finset att :=
ARAe.rec_on e S -- relnm
              (λ e1 e2 e1S e2S, e1S ∪ e2S) -- union
              (λ Y e1 e1S, e1S ∩ Y) -- proj
              (λ Y hmutc e1 e1S, e1S) -- selection
              (λ φ hinj hc e1 e1S, finset.image φ e1S) -- rename
              (λ e1 e2 e1S e2S, e1S ∪ e2S) -- join

-- def well typed: union should be on relations with equal schema
def ARA_well_typed (e : ARAe rel att) (S : rel → finset att) : Prop :=
ARAe.rec_on e (λ R, true) -- relnm
              (λ e1 e2 e1W e2W, e1W ∧ e2W ∧ (ARAschema e1 S = ARAschema e2 S)) -- union
              (λ Y e1 e1W, e1W) -- proj
              (λ Y hmutc e1 e1W, e1W) -- selection
              (λ φ hinj hc e1 e1W, e1W) -- rename
              (λ e1 e2 e1W e2W, e1W ∧ e2W) -- join

-- def semantics
def dom_assign := quotient _inst_1 → finset dom -- not assumed that assigned domain is nonempty

@[reducible] def tuple (D : dom_assign) (X : finset att) := Π (A : (↑X : set att)), (↑(D⟦A⟧) : set dom)

structure relation (D : dom_assign) (α : Type) :=
(schema : finset att)
(rel : tuple D schema → α)

/-
structure db_instance (D : dom_assign) (S : rel → finset att) (α : Type) :=
(dbI : rel → relation D α)
(schema_respect : (∀ R : rel, (dbI R).schema = S R))
-/

def db_instance (D : dom_assign) (S : rel → finset att) (α : Type) := Π R : rel, tuple D (S R) → α

def db_instance_to_rel {D : dom_assign} {S : rel → finset att} {α : Type} (I : db_instance D S α) :
rel → relation D α :=
(λ R,
{
    schema := S R,
    rel := I R
})

variables {D : dom_assign} {α : Type} [semiring α]

theorem inclusion_compat {s t : set att} (h : s ⊆ t) : compat_func (set.inclusion h) :=
begin
intro x, refl,
end

--set_option trace.simplify.rewrite true
theorem restrict_compat {f : att → att} {s t : set att} (h1 : compat_func (set.func_to_univ f)) (h2 : set.maps_to f s t) :
compat_func (set.maps_to.restrict f s t h2) :=
begin
intro x, unfold compat_func at h1, rw set_coe.forall at h1, apply h1, exact trivial,
end

theorem compat_att_eq_dom {A B : att} (h: ⟦A⟧ = ⟦B⟧) : ↥(↑(D⟦A⟧) : set dom) = ↥(↑(D⟦B⟧) : set dom) :=
congr rfl (congr_arg coe (congr_arg D h))

theorem mut_compat_eq_dom {Y : set att} (h : mut_compat Y) (A B : Y) : ⟦(A : att)⟧ = ⟦(B : att)⟧ :=
begin
apply quotient.eq_rel.mpr, apply h, cases A, rw subtype.coe_mk, exact A_property, cases B, rw subtype.coe_mk, exact B_property,
end

theorem func_compat_eq_dom {X X' : finset att} {f : (↑X' : set att) → (↑X : set att)} (h : compat_func f)
(A : (↑X' : set att)) : ⟦(f A : att)⟧ = ⟦(A : att)⟧ :=
begin
apply quotient.eq_rel.mpr, unfold compat_func at h, rw set_coe.forall at h, cases A,
exact setoid.symm' _inst_1 (h A_val A_property),
end

def tuple_comp {D : dom_assign} {X X' : finset att} {f : (↑X' : set att) → (↑X : set att)} (t : tuple D X)
(h : compat_func f) : tuple D X' :=
(λ A, (eq.mp (compat_att_eq_dom (func_compat_eq_dom h A)) (t (f A))))

def relation_mut_eq {D : dom_assign} {X : finset att} {Y : set att} (h : mut_compat Y) (t : tuple D X) : Prop :=
(∀ A B : (↑X) ∩ Y,
let fil := (set.inclusion (set.inter_subset_left ↑X Y)) in
let fir := (set.inclusion (set.inter_subset_right ↑X Y)) in
(eq.mp (compat_att_eq_dom (mut_compat_eq_dom h (fir A) (fir B))) (t (fil A))) = t (fil B))

--set_option pp.implicit true
--set_option pp.coercions true

def rel_one (X : finset att) : relation D α :=
{
    schema := X,
    rel := (λ t, 1)
}
def rel_union (r r' : relation D α) : relation D α :=
{
    schema := r.schema ∪ r'.schema,
    rel := (λ t, r.rel(tuple_comp t (inclusion_compat (finset.subset_union_left r.schema r'.schema))) +
                  r'.rel(tuple_comp t (inclusion_compat (finset.subset_union_right r.schema r'.schema))))
}
def rel_proj (r : relation D α) (Y : finset att) (hfin : fintype (tuple D r.schema)) : relation D α :=
{
    schema := r.schema ∩ Y,
    rel := (λ t, finset.sum (set.finite.to_finset (set.finite.of_fintype -- use new finsum API
           {t' : tuple D r.schema | t = tuple_comp t' (inclusion_compat (finset.inter_subset_left r.schema Y))}
           )) r.rel)
}
def rel_selection (r : relation D α) (Y : finset att) (h : mut_compat ↑Y) : relation D α :=
{
    schema := r.schema,
    rel := (λ t, if relation_mut_eq h t then (r.rel t) else 0)
}
def rel_rename (r : relation D α) (φ : att → att) (h : (compat_func (set.func_to_univ φ))) : relation D α :=
{
    schema := finset.image φ r.schema,
    rel := (λ t, r.rel(tuple_comp t (restrict_compat h (finset.maps_to_image φ r.schema))))
}
def rel_join (r r' : relation D α) : relation D α :=
{
    schema := r.schema ∪ r'.schema,
    rel := (λ t, r.rel(tuple_comp t (inclusion_compat (finset.subset_union_left r.schema r'.schema))) *
                  r'.rel(tuple_comp t (inclusion_compat (finset.subset_union_right r.schema r'.schema))))
}

-- TODO: add usual notation for the above operations

/- possibly remove -/
def bundle_rel {D : dom_assign} {α : Type} {schema : finset att} (rel : tuple D schema → α) :
relation D α :=
{
    schema := schema,
    rel := rel
}

/- possibly remove -/
def ARA_output_with_schema (e : ARAe rel att) (S : rel → finset att) (I : db_instance D S α) :
tuple D (ARAschema e S) → α :=
ARAe.rec_on e I -- relnm
              (λ e1 e2 e1W e2W, (rel_union (bundle_rel e1W) (bundle_rel e2W)).rel) -- union
              (λ Y e1 e1W, (rel_proj (bundle_rel e1W) Y pi.fintype).rel) -- proj
              (λ Y hmutc e1 e1W, (rel_selection (bundle_rel e1W) Y hmutc).rel) -- selection
              (λ φ hinj hc e1 e1W, (rel_rename (bundle_rel e1W) φ hc).rel) -- rename
              (λ e1 e2 e1W e2W, (rel_join (bundle_rel e1W) (bundle_rel e2W)).rel) -- join

-- Note: we define semantics without assuming well-typedness.
-- This requires rel_union to be defined above in a more general setting.
def ARA_output (e : ARAe rel att) (S : rel → finset att) (I : db_instance D S α) : relation D α :=
ARAe.rec_on e (db_instance_to_rel I) -- relnm
              (λ e1 e2 e1W e2W, rel_union e1W e2W) -- union
              (λ Y e1 e1W, rel_proj e1W Y pi.fintype) -- proj
              (λ Y hmutc e1 e1W, rel_selection e1W Y hmutc) -- selection
              (λ φ hinj hc e1 e1W, rel_rename e1W φ hc) -- rename
              (λ e1 e2 e1W e2W, rel_join e1W e2W) -- join

-- Prove that output relation has schema ARAschema e S
theorem ARA_sound_schema (e : ARAe rel att) (S : rel → finset att) (I : db_instance D S α) :
(ARA_output e S I).schema = ARAschema e S :=
begin
induction e,
case relnm : {exact rfl},
case union : {
    change (ARA_output (e_a.union e_a_1) S I) with
      rel_union (ARA_output (e_a) S I) (ARA_output (e_a_1) S I),
    change (ARAschema (e_a.union e_a_1) S) with (ARAschema e_a S) ∪ (ARAschema e_a_1 S),
    unfold rel_union,
    rw [← e_ih_a, ← e_ih_a_1],
},
case proj : {
    change (ARA_output (ARAe.proj e_Y e_a) S I) with rel_proj (ARA_output e_a S I) e_Y pi.fintype,
    change (ARAschema (ARAe.proj e_Y e_a) S) with (ARAschema e_a S) ∩ e_Y,
    unfold rel_proj,
    rw [← e_ih],
},
case selection : {exact e_ih},
case rename : {
    change (ARA_output (ARAe.rename e_φ e_hinj e_hc e_a) S I) with rel_rename (ARA_output e_a S I) e_φ e_hc,
    change (ARAschema (ARAe.rename e_φ e_hinj e_hc e_a) S) with finset.image e_φ (ARAschema e_a S),
    unfold rel_rename,
    rw [← e_ih],
},
case join : {
    change (ARA_output (e_a.join e_a_1) S I) with
      rel_join (ARA_output (e_a) S I) (ARA_output (e_a_1) S I),
    change (ARAschema (e_a.join e_a_1) S) with (ARAschema e_a S) ∪ (ARAschema e_a_1 S),
    unfold rel_join,
    rw [← e_ih_a, ← e_ih_a_1],
},
end

theorem rel_union_comm (r r': relation D α) : rel_union r r' = rel_union r' r := sorry

end ARA
end ARA
