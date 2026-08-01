/- Finite Axiomatization of intuitionistic NF set theory -/
/- Michael Beeson -/
/- this file contains all the uses of comprehension,  so one 
    can verify they are all stratified instances.  -/

import tactic.basic 
import mario 

set_option default_priority 100
reserve infix ` ∈ ` : 49
reserve infix ` ⊆ ` : 49
reserve infix ` ⊂ ` : 49
reserve infix ` ∪ ` : 50
reserve infix ` ∩ ` : 50
reserve infix ` × ` : 50 
reserve infix ` ⊕ ` : 60  --addition on Church numbers 
reserve infix ` ⊗ ` : 61  --multiplication on Church numbers 
reserve infix ` - ` : 51 
reserve infix ` ≤ℍ `: 49
reserve infix ` <ℍ `: 49
reserve infix ` ≤ℕ `: 49
reserve infix ` <ℕ `: 49
reserve infix ` ≺ ` : 49 
reserve infix ` ≼ ` : 49 
reserve infix ` ⋖ ` : 49
reserve infix ` ⪯ `: 49


/- set_option pp.all true -/

class  Model (M:Type) := 
(𝔽:M)      -- finite Frege cardinals, least class closed under inhabited successor
(ℕℕ:M)      -- Church numbers
(STEM:M)
(LOOP:M → M)
(ℍ:M)      -- least class closed under nonempty successor
(succ:M)   --graph of 𝕊 
(𝕊:M → M)  --Frege successor
(S:M → M)  --Church successor
(Ap:M → M → M)  -- Ap f x is function application, f(x) informally
(Λ:M)
(zero:M) 
(one:M)
(two:M)
(three:M)
(four:M)
(five:M)
(six:M)
(FUNC:M)
(id:M)
(ChurchZero:M)  --Church zero
(mem : M → M → Prop)   
(subset: M → M → Prop) 
(proper_subset: M → M → Prop)
(le: M → M → Prop)
(leH: M → M → Prop)
(lessthan: M → M → Prop)
(lessthanH: M → M → Prop)
(lessthanN: M → M → Prop)
(lessdot: M → M → Prop)
(ledot: M → M → Prop)
(leN: M → M → Prop) 
(prec: M → M → Prop)
(preceq: M → M → Prop)
(complement: M → M)
(𝕍 : M) 
(binary_union : M → M → M)
(addition: M → M → M)
(ChurchAddition: M → M → M)
(ChurchMultiplication: M → M → M)
(divides: M → M → Prop) 
(union: M → M)
(intersection : M → M → M)
(restrict: M → M → M ) 
(imp: M → M → M)
(pair: M → M → M) 
(single: M → M)
(ordered_pair: M → M → M) 
(triple: M → M → M → M) 
(product: M → M → M)
(Rel: M →  Prop)
(dom: M → M)
(range:M → M)
(univ: M → M)
(inv: M → M )
(minus: M → M → M)
(join: M → M → M) 
(SI: M → M )  /- singleton_image -/
(subset_relation: M)
(equality_relation: M)
(setof: (M→Prop)→ M)
(proj1: M)
(proj2: M)
(USC: M → M)
(SSC: M → M)
(SC: M → M)
(single_definition : ∀ x, single x = pair x x)
(infix  ∈ :=  mem)
(infix  + := addition)
(infix - := minus )
(infix ⊕:= ChurchAddition)
(infix ⊗:= ChurchMultiplication)
(infix ∪ := binary_union)
(infix ∩ := intersection)
(infix × := product)
(infix ⊆ := subset)
(infix ⊂ := proper_subset)
(infix <ℕ := lessthanN)
(infix ≤ℕ := leN)
(infix ≺ := prec) 
(infix ≼ := preceq) 
(infix ⋖ := lessdot)
(infix ⪯ := ledot)

(notation `{` a `,` b `}` := pair a b)
(notation ` ‹ ` a `,` b ` › ` := ordered_pair a b)
(extensionality_axiom:  ∀ a b, (∀ x, (x ∈ a ↔ x ∈ b)) → a=b)
(binary_union_axiom:   ∀ a b x, (x ∈ a ∪ b ↔ x ∈ a ∨  x ∈ b))
(intersection_axiom:  ∀ a b x, (x ∈ a ∩  b ↔ x ∈ a ∧ x ∈ b))
(complement_axiom:  ∀ a x, (x ∈ complement a ↔ ¬ x ∈ a))
(implication_axiom:    ∀ a b x, (x ∈ imp a b ↔ (x ∈ a → x ∈ b)))
(emptyset_axiom:   ∀ x, (¬ x ∈ Λ ))
(pairing_axiom:  ∀ x a b, (x ∈ {a,b} ↔ (x = a ∨  x = b)))
(ordered_pair_definition:   ∀ x y, (‹x,y›   = {single x , {x, y}})) 
(triple_definition: ∀ (x y z), triple x y z = ‹ ‹ x,y ›, single (single z) › )
(domain_axiom:  ∀ R, (Rel R → ∀ x, (x ∈ dom R ↔ ∃ y, (‹x,y› ∈ R))))
(range_axiom:  ∀ R, (Rel R → ∀ y, (y ∈ range R ↔ ∃ x, (‹x,y› ∈ R))))
(univ_axiom: ∀ R, (Rel R → ∀ x, (x ∈ univ R ↔ ∀ y, (‹x,y› ∈ R))))
(V_definition:   ∀ x, ( x ∈ 𝕍 ))
(Rel_definition:  ∀ X, ( Rel X ↔ ∀ z, (z ∈ X →  ∃ a b,(z = ordered_pair a b))))
(product_axiom:   ∀ x y u, (u ∈ x × y ↔ ∃ a b, (a ∈ x ∧ b ∈ y ∧ u = ordered_pair a b )))
(inverse_axiom1:  ∀ R, Rel R → Rel (inv R))
(inverse_axiom2:   ∀ R, (Rel R → ∀ x y, (ordered_pair x y ∈ inv R ↔ ordered_pair y x ∈ R)))
(equality_relation_axiom1: Rel equality_relation)
(equality_relation_axiom2:  ∀ x y, ( ordered_pair x y ∈ equality_relation ↔ x = y ))
(subset_definition:   ∀ x y, (x ⊆ y ↔ ∀ z, (z ∈ x → z ∈ y)))
(proper_subset_definition: ∀ x y, (x ⊂ y ↔ x ⊆ y ∧ ¬ (x=y)))
(subset_relation_axiom1: Rel subset_relation) 
(subset_relation_axiom2:  ∀ x y, (ordered_pair x y  ∈ subset_relation ↔ x ⊆ y))
(union_axiom:   ∀ (x y:M), (x ∈ union y ↔ ∃ (z:M), (z ∈ y ∧ x ∈ z)))
(le_definition: ∀ (x y:M), (le x y  ↔ ∃ (a b), a ∈ x ∧ b ∈ y ∧ a ⊆ b ∧  b = binary_union a (minus b a)))
(lessthan_definition: ∀ (x y:M), (lessthan x y ↔ le x y ∧ ¬ (x = y))) 
(ledot_definition: ∀ (x y:M), (ledot x y  ↔ ∃ (a b), a ∈ x ∧ b ∈ y ∧ a ⊆ b ))
(lessdot_definition: ∀ (x y:M), (lessdot x y ↔ ledot x y ∧ ¬ (y ⪯ x) ∧ ∃ (a b), a ∈ x ∧ b ∈ y ∧ a ⊆ b ∧ ∃ (w:M), w ∈ b-a))
(leH_definition: ∀ (x y:M), (leH x y ↔ x ∈ ℍ ∧ y ∈ ℍ ∧ ∃ k, k ∈ ℍ ∧  x + k = y))
(lessthanH_definition: ∀ (x y:M), (lessthanH x y ↔ leH x y ∧ ¬ x = y))
(restrict_definition: ∀ f x,( restrict f x = intersection f (product x 𝕍 )))
(singleton_image_axiom1: ∀ R, (Rel R → Rel (SI R)))
(singleton_image_axiom2:  ∀ R, (Rel R  → ∀ x y, (ordered_pair x y  ∈ SI R ↔ 
              ∃ a b, (x = single a  ∧ y = single b ∧ ordered_pair a b  ∈ R))))
(join_axiom: ∀ R S, (Rel R → Rel S → ∀ x, ( x ∈  join R S ↔ 
             ∃ a b c, (x = ordered_pair a c ∧  ordered_pair a b   ∈ R ∧ ordered_pair b c  ∈ S))))
(proj1_axiom: ∀ z, (z ∈ proj1 ↔ ∃ x y, 
                (z = ordered_pair (ordered_pair x y) (single (single x)))))             
(proj2_axiom: ∀ z, (z ∈ proj2 ↔ ∃ x y, 
                (z = ordered_pair (ordered_pair x y) (single (single y)))))
(usc_definition:  ∀ z, (USC z) = dom (SI (z × z) ))
(minus_definition: ∀ a b,( minus a b )= ( a ∩ (complement b)))
(zero_definition: zero = single Λ )
(one_definition: one = 𝕊 zero)
(two_definition: two = 𝕊 one) 
(three_definition: three = 𝕊 two) 
(four_definition: four = 𝕊 three)
(five_definition: five = 𝕊 four)  
(six_definition: six = 𝕊 five) 
(addition_definition: ∀ (x y:M), x + y = setof(λ z:M , ∃ (u v:M), z = (u ∪ v) ∧ u ∈ x ∧ v ∈ y ∧ u ∩ v = Λ ))
(ssc_definition: ∀ x u,  (u ∈ SSC x ↔ u ⊆ x ∧ (x = (u ∪ (minus x u)))))
(sc_definition: ∀ x u, (u ∈ SC x ↔ u ⊆ x))
(succ_definition: ∀ u, 𝕊 u =  setof(λ y, ∃ x a,(x ∈ u ∧ ¬ a ∈ x ∧ y = (x ∪ (single a)))))
(succ1: Rel succ)
(succ2: ∀ u v, (‹ u,v› ∈ succ ↔ v = 𝕊 u))
(F_members: ∀ x, (x ∈ 𝔽 ↔ ∀ w,((zero ∈ w ∧ ∀ u, (u ∈ w → (∃ v, v ∈ 𝕊 u) → (𝕊 u ∈ w))) → x ∈ w)))
(H_members: ∀ x, (x ∈ ℍ ↔ ∀ w,((zero ∈ w ∧ ∀ u, (u ∈ w → (¬ 𝕊 u = Λ ) → (𝕊 u ∈ w))) → x ∈ w)))
(N_members: ∀ x, (x ∈ ℕℕ ↔ ∀ w,(ChurchZero ∈ w ∧ ∀ u, (u ∈ w →S u ∈ w)) → x ∈ w))
(comprehension: ∀f:M→Prop, ∀ z,(z∈ (setof f) ↔ (f z))) 
(Ap_definition: ∀ (f x:M),  Ap f x  = setof(λ(u:M), ∃ (y:M), ‹ x,y › ∈ f ∧ u ∈ y))
(FUNC_definition: FUNC = setof(λ(f:M), ∀ (x y z:M), ‹ x,y › ∈ f → ‹ x,z› ∈ f → y = z))
(Church_successor: S = λ (z:M),  setof(λ(v:M), z ∈ FUNC ∧ 
 ∃ (f p:M), v = ‹ f,p› ∧ f ∈ FUNC ∧ 
 ∀ (u:M), u ∈ p ↔ 
 ∃ (x w t q:M), u = ‹ x,w› ∧ t ∈ FUNC ∧ ‹ f,t›  ∈ z ∧ ‹ x,q› ∈ t ∧ ‹ q,w › ∈ f ))
 (identity_definition: ∀ (u:M), u ∈ id ↔ ∃ (x:M), u = ‹ x,x› )
 (ChurchZero_definition: ∀ (u:M), u ∈ ChurchZero ↔ ∃ (f:M), u = ‹ f, id › )
 --(ChurchAddition_definition): ∀ (u:M), u ∈ x ⊕ y ↔ 
 (ChurchZero_equation: ∀ (x:M), x ∈ ℕℕ → x ⊕ ChurchZero = x)
 (ChurchAddition_equation: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ⊕ S y = S (x ⊕ y))
 -- later if desired I can define ChurchAddition explicitly and prove these two 
 (ChurchMultiplicationBase: ∀ (x:M),x ∈ ℕℕ → x ⊗ ChurchZero = ChurchZero)
 (ChurchMultiplicationEquation: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ⊗ S y = x ⊗ y ⊕ x)
 (ChurchOrder2: ∀ (x y:M), x ≤ℕ y ↔ ∃ (n:M), n ∈ ℕℕ ∧ x ⊕ n = y)
 (ChurchOrder: ∀ (x y:M), x <ℕ y ↔ ∃ (n:M), n ∈ ℕℕ ∧ x ⊕ S n = y)
 (StemDefinition: ∀(x:M), x ∈ STEM ↔ x ∈ ℕℕ ∧ ∀ (w:M), ChurchZero ∈ w → ( ∀ (u:M), u ∈ ℕℕ → u ∈ w → (∀ (v:M), v ∈ ℕℕ → S u = S v → u = v) → S u ∈ w)→ x∈ w)
 (preceq_definition: ∀ (x y:M), x ≼ y  ↔ ∀ (w:M), ℕℕ = (w ∪ (ℕℕ -w)) → ( ∀(u:M), u ∈ w → ( ∀(v:M), v ∈ ℕℕ → v <ℕ u → S u = S v → u = v) → S u ∈ w ) → x ∈ w → y ∈ w)
 (prec_definition: ∀ (x y:M), x ≺ y ↔ x ≼ y ∧ ¬ x = y) 
 (LoopDefinition: ∀(x n:M), x ∈ LOOP n ↔ x ∈ ℕℕ ∧ ∀ (w:M), n ∈ w → (∀ (u:M), u ∈ w → S u ∈ w) → x ∈ w)
 (divides_definition: ∀ (x y:M), divides x y ↔ x ∈ ℕℕ ∧ y ∈ ℕℕ ∧ x ≼ y ∧ ∃ (z:M),z ∈ ℕℕ ∧ x ⊗ z = y )

 /- end of class definition because next line doesn't declare a member -/

variables (M:Type) [Model M] (a b x y z u v w X R W: M)

open Model 
infix + := addition 
infix ⊕ := ChurchAddition
infix ⊗ := ChurchMultiplication
infix ∈ :=  mem 
infix ∪ := binary_union
infix ∩ := intersection
infix × := product
infix ⊆ := subset
infix ⊂ := proper_subset
infix - := minus  
infix ≤ := le 
infix < := lessthan 
infix  ≤ℍ := leH 
infix  <ℍ := lessthanH 
infix  ≤ℕ := leN 
infix  <ℕ := lessthanN 
infix ≺ := prec 
infix ≼ := preceq 
infix ⋖ := lessdot
infix ⪯ := ledot

notation `{` a `,` b `}` := pair a b
notation ` ‹ ` a `,` b ` › ` := ordered_pair a b
notation a ` ⋖ ` b := lessdot a b

def FINITE:M := setof (λ x, ( ∀ w,( Λ ∈ w ∧  (∀ u a, ((¬ (a ∈ u)) ∧ u ∈ w → (u ∪ (single a)) ∈ w))→ x ∈ w)))
def DECIDABLE:M := setof(λ x,( ∀ u v, (u∈ x ∧ v ∈ x → u=v ∨ ¬ (u = v)))) 
def EMPTY_OR_INHABITED:M := setof(λ x,(x = Λ ∨ ∃ u,(u ∈ x)))
def IDENTITY(z:M) := setof(λ x,(∃ u, (u ∈ z ∧ x = ‹ u, u ›  )))
def W5:M  := setof(λ y, y ∈ FINITE M ∧ ∀ x:M,(y = (USC x) → x ∈ FINITE M))
def W5b:M  := setof(λ x, x ∈ FINITE M ∧ (USC x) ∈ FINITE M) 
def W6:M := setof(λ x, x ∈ FINITE M ∧  ∀ y,(y ∈ FINITE M → x ∩ y = Λ → x ∪ y ∈ FINITE M) ) 
def W10:M := setof(λ x, x ∈ FINITE M ∧ SSC x ∈ FINITE M) 
def f10(x c:M) := setof(λ z, ∃ (u y:M), z = ‹ u, y › ∧ u ∈ SSC x ∧ y = (u ∪ (single c)))
def separable_subset(x y:M):= x ⊆ y ∧ y = (x ∪ (y - x)) 
def W11:M := setof(λ Y, Y ∈ FINITE M ∧ ∀ X,(Y ⊆ X → X ∈ FINITE M → separable_subset M Y X))
def W12:M := setof(λ X, X ∈ FINITE M ∧ ∀ Y,(Y ⊆ X → separable_subset M Y X → Y ∈ FINITE M)) 
def W13:M := setof(λ X, X ∈ FINITE M ∧ ∀ Y,(Y ∈ FINITE M → Y ⊆ X → (X-Y) ∈ FINITE M))
def W14:M → M → M:= λ(R X:M), ( setof(λ (b:M), b ∈ FINITE M ∧ b ⊆ X ∧  X ∈ DECIDABLE M ∧ ( ∀ (u z:M),(u ∈ X → z ∈ X → ‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R)) →∀ (z:M), (z ∈ X → (∃ u,(u ∈ b ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ b ∧ ‹ u,z› ∈ R) )))   
def W115:M → M → M → M:= λ(R X Y:M), ( setof(λ (b:M), b ∈ FINITE M ∧ b ⊆ X ∧  X ∈ DECIDABLE M ∧ ( ∀ (u z:M),(u ∈ X → z ∈ Y → ‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R)) →∀ (z:M), (z ∈ Y → (∃ u,(u ∈ b ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ b ∧ ‹ u,z› ∈ R) )))  
def Z17:M := setof(λ x, x ∈ 𝔽 ∧ ∀ y,(y ∈ x → y ∈ FINITE M)) 
def separable(u x:M) := x = (u ∪ (x-u))

def Z61:M := setof(λ μ, μ ∈ 𝔽 ∧  ∀ (κ :M), κ ∈ 𝔽 →  (∃ u, u ∈ κ + μ ) → κ + μ ∈ 𝔽 )
def Z62a:M := setof(λ m, m ∈ 𝔽  ∧ ((∃ p:M, p ∈ 𝔽 ∧  m = p + p + p) ∨ (∃ p:M, p ∈ 𝔽 ∧ m = p + p + p + one)
∨ (∃ p:M,  p ∈ 𝔽 ∧ m = p + p + p+two)) )
def Z62:M := setof(λ m, m ∈ 𝔽 ∧  ∀ (p q:M), p ∈ 𝔽  → q ∈ 𝔽 → (m = p + p + p → m = q + q + q + one → false) ∧ (m = p + p + p → m = q + q + q + two → false) ∧ (m = p + p + p + one → m = q + q + q + two  → false))

def Z18:M := setof(λ κ, κ ∈ 𝔽 ∧ ∃ u, u ∈ κ) 
def Z24:M := setof(λ κ, κ ∈ 𝔽 ∧ (κ  = zero ∨ ∃ μ:M, μ ∈ 𝔽 ∧ κ = 𝕊 μ ))
def Z42(f b:M):M := setof(λ z,∃ (u v:M), z = ‹ u,v› ∧ u ∈ SSC b ∧ v = range(restrict f u)) 
def Z43(f b:M):M := setof(λ z,∃ (u v:M), z = ‹ u,v› ∧ u ∈ SC b ∧ v = range(restrict f u)) 
def W48(b:M):M := setof(λ z, z ∈ SSC b →   ∀(x:M),(x∈ SSC b → x ⊆ z ∨ ¬ x ⊆ z))
def W16:M := setof(λ x, x ∈ FINITE M ∧  ((∀ p,(p ∈ x → p ∈ FINITE M)) →  (∀ (p v:M), p ∈ x → v ∈ x → ¬ p = v → (p ∩ v = Λ) ) → (union x) ∈ FINITE M ))

lemma Z61_members: ∀(μ : M), μ ∈ Z61 M ↔ μ ∈ 𝔽 ∧  ∀ (κ :M), κ ∈ 𝔽 → (∃ u, u ∈ κ + μ ) → κ + μ ∈ 𝔽:=
  assume μ,
  begin
    unfold Z61,
    rw comprehension,
  end 

lemma Z62a_members: ∀ (m:M), m ∈ Z62a M ↔  m ∈ 𝔽  ∧ ((∃ p:M,  p ∈ 𝔽 ∧  m = p + p + p) ∨ (∃ p:M,  p ∈ 𝔽 ∧ m = p + p + p + one)
∨ (∃ p:M,  p ∈ 𝔽 ∧ m = p + p + p+two)):=
  assume m,
  begin 
    unfold Z62a,
    rw comprehension,
  end 

lemma Z62_members: ∀ (m:M), m ∈ Z62 M ↔ m ∈ 𝔽 ∧  ∀ (p q:M), p ∈ 𝔽  → q ∈ 𝔽 →
  (m = p + p + p → m = q + q + q + one → false) ∧ 
  (m = p + p + p → m = q + q + q + two → false) ∧
  (m = p + p + p + one →  m = q + q + q + two  → false):=
  assume m, 
  begin 
    unfold Z62,
    rw comprehension, 
  end 

lemma W16_members: ∀ (x:M), x ∈ W16 M ↔  x ∈ FINITE M ∧ 
((∀ u,(u ∈ x → u ∈ FINITE M)) →  
(∀ (u v:M), u ∈ x → v ∈ x → ¬ u = v → u ∩ v = Λ ) → 
union x ∈ FINITE M):=
  assume x,
  begin
    unfold W16,
    rw comprehension, 
  end 

lemma addition_members: ∀(x y z:M), z ∈ x + y ↔ ∃ (u v:M), z = (u ∪ v) ∧ u ∈ x ∧ v ∈ y ∧ u ∩ v = Λ:=
  assume x y z,
  begin
    rw addition_definition,
    rw comprehension, 
  end 

lemma W48_members: ∀(b z:M), (z ∈ (W48 M b) ↔z ∈ SSC b →  ∀(x:M),x ∈ SSC(b) → x ⊆ z ∨ ¬ x ⊆ z) :=
  assume b z,
  begin
    unfold W48,  
    rw comprehension, 
  end 

lemma Z42_members: ∀ (f a :M), ∀ (z:M),( z ∈ (Z42 M f a) ↔ ∃ (u v:M), z = ‹ u,v› ∧ u ∈ SSC a ∧ v = range(restrict f u)):=
  assume f a,
  begin
    unfold Z42,
    intro z, 
    rw comprehension, 
  end 

lemma Z43_members: ∀ (f a :M), ∀ (z:M),( z ∈ (Z43 M f a) ↔ ∃ (u v:M), z = ‹ u,v› ∧ u ∈ SC a ∧ v = range(restrict f u)):=
  assume f a,
  begin
    unfold Z43,
    intro z, 
    rw comprehension, 
  end 

lemma Z24_members: ∀ (κ :M),(κ ∈  Z24 M ↔ κ ∈ 𝔽 ∧ (κ  = zero ∨ ∃ (μ:M), μ ∈ 𝔽 ∧ κ = 𝕊 μ )):=
  assume κ,
  begin
    unfold Z24,
    rw comprehension,
  end 

lemma Z16_members: ∀ (x:M), (x ∈ Z17 M ↔ x ∈ 𝔽 ∧ ∀ y,(y ∈ x → y ∈ FINITE M)):=
  assume x,
  begin
    unfold Z17,
    rw comprehension,
  end 

lemma Z18_members: ∀ (κ:M), (κ ∈ Z18 M ↔ κ ∈ 𝔽 ∧ ∃ u, u ∈ κ):=
  assume κ,
  begin 
    unfold Z18,
    rw comprehension,
  end 
 
lemma W11_members: ∀ (Y:M),(Y ∈ W11 M  ↔ Y ∈ FINITE M ∧ ∀ X,(Y ⊆ X → X ∈ FINITE M → separable_subset M Y X) ):=
  assume X,
  begin
    unfold W11, 
    rw comprehension, 
  end

lemma W12_members: ∀ (X:M),(X ∈ W12 M ↔X ∈ FINITE M ∧ ∀ Y,(Y ⊆ X → separable_subset M Y X → Y ∈ FINITE M) ):=
  assume X,
  begin
    unfold W12, 
    rw comprehension, 
  end

lemma W13_members: ∀ (X:M),(X ∈ W13 M ↔X ∈ FINITE M ∧ ∀ Y,(Y ∈ FINITE M → Y ⊆ X → (X-Y) ∈ FINITE M) ):=
  assume X,
  begin
    unfold W13, 
    rw comprehension, 
  end

lemma finite_members: ∀ x:M,
(
  (x ∈ (FINITE M)) ↔ 
   ∀ w, ( (Λ ∈ w ∧ ∀ u a, ((¬ (a ∈ u)) ∧ u ∈ w →( u ∪ (single a)) ∈ w))→ x ∈ w))
   :=
  begin
    unfold FINITE,
    intro x,
    rw ( comprehension  (λ (x : M), ∀ w, (Λ ∈ w ∧  ∀ (u a : M), (¬(a ∈ u) ∧ u ∈ w → u ∪ single a ∈ w)) → x ∈ w) ),
  end 

lemma decidable_members: ∀ x:M, (x ∈ (DECIDABLE M) ↔ 
∀ u v, (u∈ x ∧ v ∈ x → u=v ∨ ¬ (u = v))) :=
  begin
    unfold DECIDABLE,
    intro x,
    rw( comprehension (λ (x : M), ∀ (u v:M), (u∈ x ∧ v ∈ x → u=v ∨ ¬ (u = v)))), 
  end 

lemma identity_members: ∀ x z:M, (z ∈ IDENTITY M x ↔  exists u, (z = ‹ u,u› ∧ u ∈ x)):=
  assume x z,
  begin
    split,
     { intro h1,
       unfold IDENTITY at h1,
       rw comprehension at h1,
       cases h1 with u h2,
       exact exists.intro u ⟨ h2.right, h2.left⟩, 
     },
     { intro h2,
       unfold IDENTITY,
       rw comprehension, 
       cases h2 with w h3,
       cases h3 with h4 h5,
       exact exists.intro w ⟨ h5, h4⟩,   
     }
  end

lemma W5_members: ∀ y:M,(y ∈ W5 M ↔ y ∈ FINITE M ∧ ∀ x:M,(y = (USC x) → x ∈ FINITE M)):=
  assume y,
  begin
    split,
    { unfold W5, 
       rw ( comprehension (λ (y : M), y ∈ FINITE M ∧  ∀ (x : M), y = USC x → x ∈ FINITE M)),
       intro h, 
       exact h, 
    },
    { unfold W5,
      rw ( comprehension (λ (y : M), y ∈ FINITE M ∧ ∀ (x : M), y = USC x → x ∈ FINITE M)),
      intro h,
      exact h, 
    }
  end 

lemma W5b_members: ∀ x: M,(x ∈ W5b M ↔ x ∈ FINITE M ∧ USC x ∈ FINITE M):=
  assume x,
  begin
    split,
      { unfold W5b,
        rw (comprehension (λ (x:M), x∈ FINITE M ∧ USC x ∈ FINITE M)),
        intro h,
        exact h,
      },
      { unfold W5b,
        rw (comprehension (λ (x:M), x∈ FINITE M ∧ USC x ∈ FINITE M)),
        intro h,
        exact h,
      }
  end

lemma W6_members: ∀ x: M,(x ∈ W6 M ↔ x ∈ FINITE M ∧  ∀ y,(y ∈ FINITE M → x ∩ y = Λ → x ∪ y ∈ FINITE M) ):=
  assume x,
  begin
    split,
      {  
        unfold W6, 
        intro h,

        rw (comprehension (λ (x:M), x ∈ FINITE M ∧  ∀ y,(y ∈ FINITE M → x ∩ y = Λ → x ∪ y ∈ FINITE M) ) ) at h, 
        exact h, 
      },
      { unfold W6, 
        rw (comprehension (λ (x:M), x ∈ FINITE M ∧  ∀ y,(y ∈ FINITE M → x ∩ y = Λ → x ∪ y ∈ FINITE M) )),
        intro h,
        exact h,
      }
  end

lemma W10_members: ∀ x: M, x ∈ W10 M ↔ x ∈ FINITE M ∧ SSC x ∈ FINITE M :=
  assume x,
  begin
    unfold W10,
    rw comprehension (λ x, x∈ FINITE M ∧ SSC x ∈ FINITE M), 
  end

lemma W14_members: ∀ (R X B:M), B ∈ (W14 M R X) ↔
 B ∈ FINITE M ∧  B ⊆ X ∧ X ∈ DECIDABLE M ∧  
            ( ∀ (u z:M),(u ∈ X → z ∈ X → ‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R)) →
            ∀ (z:M), (z ∈ X → (∃ u,(u ∈ B ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ B ∧ ‹ u,z› ∈ R) ) :=
assume R X B,
begin
  split,
  { 
    intro h,
    unfold W14 at h,
    rw (comprehension) at h,
    exact h, 
  },
  {
    intro h,
    unfold W14,
    rw comprehension,
    exact h,  
  }
end

lemma W115_members: ∀ (R X Y B:M), B ∈ (W115 M R X Y) ↔
 B ∈ FINITE M ∧  B ⊆ X ∧ X ∈ DECIDABLE M ∧  
            ( ∀ (u z:M),(u ∈ X → z ∈ Y → ‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R)) →
            ∀ (z:M), (z ∈ Y → (∃ u,(u ∈ B ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ B ∧ ‹ u,z› ∈ R) ) :=
assume R X Y B,
begin
  split,
  { 
    intro h,
    unfold W115 at h,
    rw (comprehension) at h,
    exact h, 
  },
  {
    intro h,
    unfold W115,
    rw comprehension,
    exact h,  
  }
end

lemma f10_members: ∀ x c z:M, (z ∈ f10 M x c ↔ ∃ (u y:M), z = ‹ u,y › ∧  u ∈ SSC x ∧ y = (u ∪ (single c))):=
  assume x c z,
  begin
    split, 
      { intro h,
        unfold f10 at h,
        rw (comprehension) at h,
        cases h with u h2,
        cases h2 with y h3,
        use u, use y, 
        rcases h3 with ⟨ h4, h5, h6⟩,
        exact ⟨ h4, h5, h6⟩, 
      },
      { unfold f10,
        intro h,
        cases h with u h2,
        cases h2 with y h3,
        rcases h3 with ⟨ h4, h5, h6⟩, 
        rw comprehension,
        use u, use y,
        exact ⟨h4,h5, h6⟩, 
      }
  end

lemma single_definition_reverse : ∀ x:M, {x,x}  = single x :=
   λ x, eq.symm(single_definition x)

 example: x ∈ {y,y} → x ∈ single y := by {intro, rwa single_definition y}

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end

lemma singleton0: ∀ x y:M, (x ∈ single y ↔ x ∈ {y,y}):=
  assume x y:M,
  begin
    rw single_definition, 
  end
      
lemma singleton1 : ∀ x y:M, (x ∈ single y ↔ x = y) :=
  assume x y:M,
  iff.intro
    ( assume h:x ∈ single y,
      or.elim
        ((pairing_axiom x y y).1 ((singleton0 M x y).1 h))
             (λ q, q)
             (λ q, q)
    )
    ( assume h:x=y,
      (singleton0 M x y).2 
      ( (pairing_axiom x y y).2  (or.inl h))          
    )

lemma pair_equality1: ∀ x y a b:M, ({x,y} = {a,b} → 
                                 (x = a ∧ y = b) ∨ (x=b ∧ y = a)) :=
  assume x y a b,
  assume h:{x,y} = {a,b},
  have q: ∀ u:M, (u ∈ {x,y} ↔ u ∈ {a,b}), from
    begin
      rewrite h,
      exact λ  u, iff.intro (λ  z, z) ( λ  z,z )
    end,
  begin 
    have qx:= q x, 
    have qy:= q y,
    have qa:= q a,
    have qb:= q b, 
    rw pairing_axiom at qx,
    rw pairing_axiom at qy,
    rw pairing_axiom at qa,
    rw pairing_axiom at qb, 
    have r := qx.1 (or.inl rfl), 
    rw pairing_axiom at r, 
    have s := qy.1 (or.inr rfl),
    rw pairing_axiom at s,
    rw pairing_axiom at qa,
    rw pairing_axiom at qb,
    have u := qa.2 (or.inl rfl),
    have v:= qb.2 (or.inr rfl),
    cases r with hxa hxb,
      { cases s with hya hyb,
        { 
          cases v with hbx hby, 
          { right,
            split,
            {
              symmetry, 
              exact hbx,
            },
            {
              exact hya,
            }
          },
          { left, 
            split,
            { 
              exact hxa,
            },
            {
              symmetry,
              exact hby,
            }
          },
        },
        { 
          exact or.inl (and.intro hxa hyb),
        }
      },
      { cases s with hya hyb,
          {
            rw hxb, rw hya,exact or.inr (and.intro rfl rfl), 
          },
          {
            rw hxb, rw hyb, rw hxb at u, rw hyb at u, 
            right,
            split,
            {
              exact refl b,
            },
            {
              symmetry,
              cases u with h3 h4,
              {
                exact h3,
              },
              {
                exact h4,
              }
            }
          }
      }
  end

lemma pair_sym: ∀ a b:M, {a,b} = {b,a} :=
  assume a b,
  begin 
    suffices h: ∀ u:M, (u ∈ {a,b} ↔ u ∈ {b,a}), from
      extensionality_axiom {a,b} {b,a} h,
    show  ∀ u:M, (u ∈ {a,b} ↔ u ∈ {b,a}),  from 
    assume u,
    begin 
      rw (pairing_axiom u a b),
      rw (pairing_axiom u b a),
      exact iff.intro
        ( λ h, h.elim (λ j, or.inr j) (λ j, or.inl j))
        ( λ h, h.elim (λ j, or.inr j) (λ j, or.inl j)),  
    end   
  end

lemma pair_equality2: ∀ x y a b:M, ((x = a ∧ y = b) ∨ (x=b ∧ y = a)→ {x,y} = {a,b}) :=
  assume x y a b,
  assume h:(x = a ∧ y = b) ∨ (x=b ∧ y = a),
    begin
      cases h with h1 h2,
        rewrite [h1.1, h1.2],
        rewrite [h2.1, h2.2, pair_sym M b a],
    end

lemma pair_equality: ∀ x y a b:M, ({x,y} = {a,b} ↔  (x = a ∧ y = b) ∨ (x=b ∧ y = a)) :=
  assume x y a b,
  iff.intro (pair_equality1 M x y a b) ( pair_equality2 M x y a b )

lemma p_or_p (p:Prop): p ∨ p ↔ p:=
  iff.intro (λ h, h.elim (λ hp:p, hp) (λ hp:p,hp) ) 
            (λ hp:p, or.inl hp)

lemma p_and_p (p:Prop): p ∧ p ↔ p:=
  iff.intro (λ h, h.1)  (λ h, and.intro h h) 

lemma singleton_equality: forall x y:M, single x = single y ↔ x = y:=
   assume x y,
   begin
    rw single_definition x,
    rw single_definition y,  
    rw pair_equality M x x,
    split,
    {
      intro h, 
      cases h with h2 h3,
      {
        exact h2.left,
      },
      {
        exact h3.left, 
      }
    },
    {
      intro h, 
      left,
      exact ⟨ h, h⟩, 
    }
    
   end

/- properties of ordered pairs -/
lemma ordered_pair_equality: ∀ x y a b:M, ‹ a, b › = ‹ x , y › ↔  a=x ∧ b=y :=
      assume x y a b,
      begin 
        apply iff.intro,
          { rw (ordered_pair_definition x y),
            rw (ordered_pair_definition a b),
            rw (single_definition a),
            rw (single_definition x),
            rw (pair_equality M {a,a} {a,b} {x,x} {x,y}),
            rw (pair_equality M a a x x),
            rw (pair_equality M a b x y),
            rw (pair_equality M a a x y),
            rw (pair_equality M a b x x),
            intro h,
            cases h with h2 h3,
            {
              cases h2 with h4 h5,
              cases h4 with h6 h7,
              {
                split,
                {
                  exact h6.left,
                },
                {
                  cases h5 with h8 h9,
                  {
                    exact h8.right,
                  },
                  {
                    cases h9 with h10 h11,
                    cases h6 with h12 h13,
                    rw h10 at *,
                    rw h11 at *, 
                    symmetry,
                    exact h12,
                  }
                }
              },
              {
                split,
                {
                  exact h7.left,
                },
                {
                  cases h5 with h8 h9,
                  {
                    exact h8.right,
                  },
                  {
                    cases h7 with h10 h11,
                    cases h9 with h12 h13,
                    rw h12 at *,
                    rw h10 at *,
                    rw h13 at *,
                  }
                }
              } 
            },
            {
              cases h3 with h4 h5,
              simp at h5, 
              cases h5 with h6 h7,
              rw h6 at *,
              rw h7 at *,
              simp,
              simp at h4, 
              exact h4, 
            }      
          },
          { intro h,
            rw h.left,
            rw h.right,
          }
      end 


lemma relprod: ∀ x:M, Rel(x × x):=
  assume x,
  begin
    rw (Rel_definition (x × x)),
    intro z,
    rw (product_axiom x x z),
    intro h,
    apply exists.elim h, 
    intros a h2,
    apply exists.elim h2,
    intros b h3,
    existsi a, 
    existsi b,
    exact h3.right.right,
  end

lemma pair_in_product: ∀ a b x y:M, ‹a,b› ∈ x × y ↔ a ∈ x ∧ b ∈ y :=
  assume a b x y,
  begin
    rw product_axiom x y ‹ a,b ›,
    apply iff.intro,
     { intro h,
       cases h with a1 h1,
       cases h1 with b1 h2,
       rw (ordered_pair_equality M a1 b1 a b) at h2,
       cases h2 with h3 h4,
       cases h4 with h5 h6,
       cases h6 with h7 h8,
       rw [h7, h8],
       exact (and.intro h3 h5),
     },
     { intro h,
       existsi a,
       existsi b,
       split,
       {
         exact h.left,
       },
       {
         exact ⟨ h.right, refl ‹ a,b› ⟩, 
       }
     }
  end 
      
lemma usc: ∀ z x:M,( x ∈ (USC z) ↔ ∃ a, (a ∈ z ∧ x = single a)):=
  assume z x,
  begin
    rw (usc_definition z),
    have q: (Rel (z × z)), from (relprod M z),
    have q2: (Rel (SI (z × z))), from (singleton_image_axiom1 ( z × z) q),
    have s: ∀ u,( (u ∈ dom (SI (z × z) )) ↔ ∃ y, ( ‹ u,y › ∈ (SI (z × z)))):=
       domain_axiom (SI(z × z)) q2,
    apply iff.intro,
    { intro h12,
        have h: ∃  y:M, (‹x, y› ∈ (SI(z × z))):= (s x).mp h12,
        cases h with y h2,
        have h3: (∃ a b:M, ( (x = (single a )) ∧ (y = (single b)) ∧ ((‹ a,b› ) ∈  (z × z)))):=
          (singleton_image_axiom2 (z × z) q x y).mp h2,
        cases h3 with a h4,
        cases h4 with b h5,
        existsi a,
        rw product_axiom z z ‹ a, b › at h5,
        cases h5 with h6 h7,
        rw h6,
        cases h7 with h8 h9,
        cases h9 with a1 h10,
        cases h10 with b1 h11, 
        rw (ordered_pair_equality M a1 b1 a b) at h11,
        cases h11 with h13 h14,
        cases h14 with h15 h16,
        cases h16 with h17 h18,
        rw h17,
        exact (and.intro h13 (eq.refl (single a1))),
    },
    { intros h6,
      cases h6 with a h7,
      rw (s x),
      existsi x,
      rw (singleton_image_axiom2 (z × z) q x x),
      existsi a,
      existsi a,
      cases h7 with h8 h9,
      rw h9,
      rw ( pair_in_product M a a z z),
      exact ⟨ refl (single a), refl (single a), h8, h8⟩, 
    }
  end

def W41 (g:M) := setof(λ w, ∃ (u v:M), w = ‹ u,v› ∧ ‹ single u, single v› ∈ g) 

lemma W41_members: ∀(g:M), Rel (W41 M g) ∧ ∀(u v:M), (‹ u,v › ∈ W41 M g ↔ ‹ single u, single v › ∈ g):=
  assume g,
  begin
    split,
    {
      rw Rel_definition, 
      intro z,
      unfold W41,
      rw comprehension,
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      use u, use v,
      exact h3.left, 
    },
    {
      intros u v,
      unfold W41,
      rw comprehension,
      split,
      {
        intro h,
        cases h with p h2,
        cases h2 with q h3,
        cases h3 with h4 h5,
        rw ordered_pair_equality at h4,
        cases h4 with h6 h7,
        rw h6 at *,
        rw h7 at *,
        exact h5, 
      },
      {
        intro h,
        use u, use v,
        exact ⟨ refl ‹ u,v › , h ⟩, 
      }
    }
  end

def W39 (y:M) := setof(λ u, single u ∈ y) 

lemma W39_members: ∀ (y u:M), u ∈ W39 M y ↔ single u ∈ y:=
  assume y u,
  begin
    unfold W39,
    rw comprehension, 
  end

 lemma minus_members: ∀ a b x:M,(x ∈ (minus a b) ↔ x ∈ a ∧ ¬ x ∈ b) :=
  assume a b x,
  begin
    rw minus_definition,
    rw intersection_axiom a (complement b) x,
    rw complement_axiom b x,
  end 

lemma inverse_SI: ∀ (f:M), ∃ (g:M),(Rel g ∧  ∀(u v:M), 
‹u,v› ∈ g ↔ ‹ single u, single v›  ∈  f):= 
  assume f,
  begin 
    use setof(λ p, ∃ u v, p = ‹ u,v› ∧ ‹ single u, single v› ∈ f),
    split,
    {
      rw Rel_definition,
      intro z,
      rw comprehension,
      intro h,
      cases h with u h1,
      cases h1 with v h2,
      cases h2 with h3 h4,
      use u, use v,
      exact h3, 
    },
    { 
      intros u v,
      rw comprehension, 
      split,
      {
        intro h,
        cases h with p h1,
        cases h1 with q h2,
        cases h2 with h3 h4,
        rw ordered_pair_equality at h3, 
        cases h3 with h5 h6,
        rw h5 at *,
        rw h6 at *,
        exact h4,
      },
      {
        intro h,
        use u, use v,
        rw ordered_pair_equality,
        split,
        {
          exact ⟨ refl u, refl v⟩, 
        },
        {
          exact h, 
        } 
      },   
    },
  end

lemma rel_proj1: (Rel  (proj1:M)):=
begin
  rw (Rel_definition proj1),
  intro,
  rw (proj1_axiom z),
  intro h,
  cases h with x h2,
  cases h2 with y h3,
  existsi ‹ x,y› ,
  existsi (single (single x)),
  assumption,
end

lemma rel_proj2: (Rel  (proj2:M)):=
begin
  rw (Rel_definition proj2),
  intro,
  rw (proj2_axiom z),
  intro h,
  cases h with x h2,
  cases h2 with y h3,
  existsi ‹ x,y› ,
  existsi (single (single y)),
  assumption,
end

def maps(f X Y:M): Prop := Rel f ∧ ( ∀ (x y:M), (x∈ X ∧ ‹ x,y › ∈ f → y ∈ Y))
   ∧ ( ∀ (x y z: M), (x ∈ X ∧ ‹ x, y › ∈ f ∧ ‹ x,z › ∈  f → y=z)) ∧ ∀ x:M,(x ∈ X → ∃ y,(y ∈ Y ∧ ‹ x,y› ∈ f))
def oneone(f X Y:M):Prop := (maps M f X Y) ∧ ( ∀ (x u y:M),(‹ x,y› ∈ f ∧ ‹ u,y › ∈ f ∧ x ∈ X → x = u)) ∧ 
                             ∀ x y:M,(‹ x,y› ∈ f ∧ y ∈ Y  →  x ∈ X)
def onto(f X Y:M):Prop:= ∀ y,(y ∈ Y → ∃ x,(x ∈ X ∧ ‹ x,y› ∈ f))

def similarity(f x y:M):Prop:=  (oneone M f x y  ∧ onto M f x y)
def similar(X Y:M):Prop:= ∃ f:M, (similarity M f X Y) 
def infinite (x:M):Prop := ∃ (y:M), y ⊆ x ∧ ¬ (x = y) ∧ similar M x y 

def Nc(x:M) := setof(λ (u:M), similar M u x) 
def W9:M := setof(λ x, x ∈ FINITE M ∧  ∀ y,( (similar M y x) → y ∈ FINITE M) ) 
def W15:M := setof(λ x, x ∈ FINITE M ∧ ∀ y, (y ⊆ x → (similar M x y) → x=y ))
def W23:M := setof(λ x, x ∈ FINITE M ∧ Nc M x ∈ 𝔽 ) 
def Z19:M := setof(λ κ, κ ∈ 𝔽 ∧ ∀ (x y:M), x ∈ κ → similar M x y → y ∈ κ)
def Z20:M := setof(λ κ, ∀ (x y:M),(x∈ κ → y ∈ κ → similar M x y))
def Z2:M := setof(λ κ, κ ∈ 𝔽 ∧ ∀ (μ:M),  μ ∈ 𝔽 → ((κ < μ ∨ κ = μ ∨ μ < κ) ∧ (¬ ( κ < μ ∧ μ < κ ))))
def W38:M := setof(λ u, ∃ (z:M), u = ‹ single z, USC z ›) 
def exp(n:M) := setof( λ u, ∃(p:M),( USC p ∈ n ∧ similar M u (SSC p)))
def exp2(n:M) := setof(λ(u:M), ∃ (p:M), USC p ∈ n ∧ similar M u (SC p))

def NC:= setof(λ(x:M), ∃(y:M), x = Nc M y)
lemma NC_members: ∀(x:M), x ∈ NC M ↔  ∃(y:M), x = Nc M y:=
  begin
    intros x,
    unfold NC,
    rw comprehension, 
  end

def Wsixpointeighthelper:M := setof(λ a, a ∈ FINITE M ∧ 
( ∀(b:M), similar M (SSC a) (USC b) → ∃(z:M), similar M a (USC z)))

lemma Wsixpointeighthelper_members: ∀ (a:M), a ∈ Wsixpointeighthelper M ↔ 
a ∈ FINITE M ∧ 
( ∀(b:M), similar M (SSC a) (USC b) → ∃(z:M), similar M a (USC z)):=
assume a,
begin
  unfold Wsixpointeighthelper,
  rw comprehension, 
end

def towergraph:= setof(λ u, ∃ (x y z:M), u = triple  x y z  ∧ y ∈ 𝔽  ∧  ∀ (Z:M),  (∀ (m:M), triple m zero m ∈ Z) ∧  ((∀ (m y z:M), triple m y z ∈ Z → (∃ u, u ∈ 𝕊 y) →  triple m (𝕊 y) ( exp M z) ∈ Z)) → u ∈ Z)
def towergraphE:= setof(λ u, ∃ (x y z:M), u = triple  x y z  ∧ y ∈ 𝔽  ∧  ∀ (Z:M),  (∀ (m:M), triple m zero m ∈ Z) ∧  ((∀ (m y z:M), triple m y z ∈ Z → (∃ u, u ∈ 𝕊 y) →  triple m (𝕊 y) ( exp2 M z) ∈ Z)) → u ∈ Z)

lemma towergraph_members1: Rel (towergraph M):= 
  begin
    unfold Rel_definition, 
    intro u,
    unfold towergraph,
    rw comprehension,
    intro h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    rw triple_definition at h5,
    use ‹ x, y ›, 
    use single (single z),
    exact h5, 
  end

lemma towergraph_members2: ∀ (u:M), u ∈ towergraph M → ∃ (x y z:M), u = triple x y z:=
  assume u,
  begin
    intro h,
    unfold towergraph at h,
    rw comprehension at h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    use x, use y, use z, 
    exact h5, 
  end 

lemma full_extensionality: ∀ a b:M,(a=b ↔  ∀ x:M,(x∈ a ↔ x ∈ b)):=
   assume a b,
   begin 
     split,
       { 
        intro h,
        rw h,
        intro x, 
        split,
        {
          intro h4,
          exact h4,
        },
         {
          intro h4,
          exact h4,
        }  
       },
       {
        exact (extensionality_axiom a b), 
       }
   end

lemma single_oneone: ∀ (a b:M), single a = single b → a = b:=
  assume a b,
  begin
    intro h,
    rw full_extensionality at h,
    rw full_extensionality,
    intro x,
    specialize h a,
    rw singleton1 at h,
    rw singleton1 at h,
    cases h with h4 h5,
    have h6: a=a:= refl a, 
    have h7:= h4 h6,
    rw h7, 
  end
  
lemma triple_equality: ∀ (x y z a b c:M), triple x y z = triple a b c ↔ x = a ∧ y = b ∧ z = c:=
  assume x y z a b c,
  begin
    repeat{ rw triple_definition},
    repeat{ rw ordered_pair_equality},
    split,
    {
      intro h,
      cases h with h2 h3,
      cases h2 with h4 h5,
      rw h4 at *,
      rw h5 at *,
      have h6:single z = single c := single_oneone M (single z) (single c) h3,
      have h7: z = c:= single_oneone M z c h6,
      rw h7 at *,
      exact⟨ refl a, refl b, refl c⟩, 
    },
    {
      intro h,
      rcases h with ⟨ h2, h3, h4⟩,
      rw h2 at *,
      rw h3 at *,
      rw h4 at *, 
      split,
      {
        exact ⟨ refl a, refl b⟩, 
      },
      {
        exact refl (single(single c)), 
      }
    }
  end

lemma towergraph_members: ∀ (x y z:M), (triple x y z ∈ towergraph M ↔ y ∈ 𝔽 ∧ 
∀ (Z:M), 
      (∀ (m:M), triple m zero m ∈ Z) ∧  
      (∀ (m y z:M), triple m y z ∈ Z →  (∃ u, u ∈ 𝕊 y) → triple m (𝕊 y) ( exp M z) ∈ Z)
      → triple x y z ∈ Z ):=
  assume x y z, 
  begin
   unfold towergraph,
   rw comprehension, 
   split,
   {
     intro h,
     cases h with p h2,
     cases h2 with q h3,
     cases h3 with r h4,
     cases h4 with h5 h6,
     rw triple_equality M at h5,
     rcases h5 with ⟨ h7, h8, h9⟩,
     rw h7 at *,
     rw h8 at *,
     rw h9 at *,
     exact h6,
   },
   {
     intro h,
     use x, use y, use z, 
     rw triple_equality,
     split,
     {
       exact ⟨ refl x, refl y, refl z⟩, 
     },
     {
       exact h, 
     }
   }
  end 



def Z_towergraph:M := setof(λ y,  y ∈ 𝔽 ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ towergraph M)
def Z_towergraph2:M := setof(λ y, y ∈ 𝔽  ∧ ∀ (x z w:M), (triple x y z ∈ towergraph M ∧ triple x y w ∈ towergraph M → z = w))
def Z_tower_defined:M := setof(λ y, y ∈ 𝔽 ∧ ∀(m:M), ∃(z:M), triple m y z ∈ towergraph M)
def Z_tower_singlevalued:M := setof(λ y, y ∈ 𝔽  ∧ ∀ (m z w:M), triple m y z ∈ towergraph M → triple m y w ∈ towergraph M → z = w )
def W81:M := setof(λ u, ∃(m y z:M), u = triple m y z ∧ triple m y z ∈ towergraph M ∧ ( (y=zero ∧ z = m)  ∨ ∃ (p v w:M), y = 𝕊 p ∧ v ∈ y ∧ triple m p w ∈ towergraph M ∧ z = exp M w))
def Z82:M := setof(λ y, y ∈ 𝔽 ∧ ∀ (m z w:M), triple m y z ∈ towergraph M → triple m y w ∈ towergraph M → z = w)

lemma Z82_members: ∀ (y:M), y ∈ Z82 M ↔ y ∈ 𝔽 ∧ ∀ (m z w:M), triple m y z ∈ towergraph M → triple m y w ∈ towergraph M → z = w:=
  assume y,
  begin
    unfold Z82,
    rw comprehension,
  end 


lemma W81_members: ∀ (u:M), u ∈ W81 M ↔ 
∃(m y z:M), u = triple m y z ∧ triple m y z ∈ towergraph M ∧
( (y=zero ∧ z = m)  ∨ ∃ (u v w:M), y = 𝕊 u ∧ v ∈ y ∧ triple m u w ∈ towergraph M ∧ z = exp M w):=
  assume u,
    begin
      unfold W81,
      rw comprehension, 
    end

 
lemma Z_towergraph_members: ∀(y:M), y ∈ Z_towergraph M ↔ y ∈ 𝔽 ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ towergraph M:=
  assume y,
  begin
    unfold Z_towergraph,
    rw comprehension, 
  end 

lemma Z_towergraph2_members: ∀ (y:M), y ∈ Z_towergraph2 M ↔ 
y ∈ 𝔽  ∧ ∀ (x z w:M), (triple x y z ∈ towergraph M 
∧ triple x y w ∈ towergraph M → z = w) :=
 assume y,
  begin
    unfold Z_towergraph2,
    rw comprehension, 
  end 

lemma Z_tower_defined_members: ∀(y:M), y ∈ Z_tower_defined M ↔
  y ∈ 𝔽 ∧ ∀(m:M), ∃(z:M), triple m y z ∈ towergraph M:=
  assume y,
  begin
    unfold Z_tower_defined,
    rw comprehension,
  end 

lemma Z_tower_singlevalued_members: ∀(y:M), y ∈ Z_tower_singlevalued M ↔
 y ∈ 𝔽  ∧ ∀ (m z w:M), triple m y z ∈ towergraph M → triple m y w ∈ towergraph M → z = w :=
  assume y,
  begin
    unfold Z_tower_singlevalued,
    rw comprehension,
  end 

def 𝕀 (m y:M):= setof(λ u,∃ (z:M), triple m y z ∈ towergraph M ∧ u ∈ z)
def Φ (m:M):= setof(λ z,  ∃ (y:M), y ∈ 𝔽 ∧ z = 𝕀 M m y ∧ ∃ (u:M), u ∈ z) 
-- Note, Φ contains the inhabited members of the range of 𝕀(m,⬝)

def Phi_members: ∀ (m z:M), z ∈ Φ M m ↔  ∃ (y:M), y ∈ 𝔽 ∧ z = 𝕀 M m y ∧ ∃ (u:M), u ∈ z:=
  assume m z,
  begin
    unfold Φ,
    rw comprehension,
  end 
def f_sixpointeight(m y:M) := setof(λ (t:M), ∃ (x u:M), t = ‹ x, u› ∧ x ≤ y ∧ u = 𝕀 M m x ∧ u ∈ 𝔽 ∧ x ∈ 𝔽 )

lemma  f_sixpointeight_members:  ∀ (m y t:M), t ∈ f_sixpointeight M m y ↔  ∃ (x u:M), t = ‹ x, u› ∧ x ≤ y ∧ u = 𝕀 M m x ∧ u ∈ 𝔽 ∧ x ∈ 𝔽 :=
  assume m y, 
  begin 
    unfold f_sixpointeight,
    intro t, 
    rw comprehension, 
  end

lemma I_members: ∀ (m y :M), u ∈ 𝕀 M m y  ↔ ∃(z:M), triple m y z ∈ towergraph M ∧ u ∈ z:=
  assume z m,
  begin
    unfold 𝕀,
    rw comprehension,      
  end 

def Z83:M := setof(λ y, y ∈ 𝔽 ∧ ∀ (m z:M), triple m y z ∈ towergraph M ↔ z = 𝕀 M m y)

lemma Z83_members: ∀ (y:M), y ∈ Z83 M ↔ y ∈ 𝔽 ∧ ∀ (m z:M), triple m y z ∈ towergraph M ↔ z = 𝕀 M m y:=
  assume y,
  begin
    unfold Z83,
    rw comprehension, 
  end 

def Z86(m:M):M := setof(λ y, y ∈ 𝔽 ∧  ((∃ u, u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽 ))

lemma Z86_members : ∀(m y:M), y ∈ Z86 M m ↔ y ∈ 𝔽 ∧ ( (∃ u, u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽) :=
  assume m y,
  begin
    unfold Z86,
    rw comprehension, 
  end

lemma exp_members: ∀(m u:M), u ∈ exp M m ↔ ∃(a:M),(USC a ∈ m ∧ similar M u (SSC a)):=
  assume m u,
  begin 
    unfold exp, 
    rw comprehension, 
  end 

lemma exp2_members: ∀(m u:M), u ∈ exp2 M m ↔ ∃(a:M),(USC a ∈ m ∧ similar M u (SC a)):=
  assume m u,
  begin 
    unfold exp2, 
    rw comprehension, 
  end 


def 𝕋 (κ:M) := setof( λ u, ∃(x:M),  x ∈ κ ∧ similar M u (USC x))

lemma T_members:∀(κ u:M), u ∈ 𝕋  M κ ↔ ∃(x:M), x ∈ κ ∧ similar M u (USC x):=
  assume κ u,
  begin
    unfold 𝕋,
    rw comprehension, 
  end 

def Z74:M := setof(λ m, m ∈ 𝔽 ∧ ∀(n:M), n∈ 𝔽 → (n+m) ∈ 𝔽 → 𝕋 M (n+m) = 𝕋 M n + 𝕋 M m)

def WFS3(a b:M):M := setof(λ x,   x ∈ FINITE M ∧  x ⊆ b →  ∀ (t:M), t ∈ a → (t ∈ x ∨ ¬ t ∈ x) )

lemma WFS3_members : ∀(a b x:M), x ∈ WFS3 M a b ↔  x ∈ FINITE M ∧  x ⊆ b 
→  ∀ (t:M), t ∈ a → (t ∈ x ∨ ¬ t ∈ x):=
  assume a b x,
  begin
    unfold WFS3, 
    rw comprehension, 
  end

lemma Z74_members: ∀ (m:M), m ∈ Z74 M ↔  m ∈ 𝔽 ∧ ∀(n:M), n∈ 𝔽 → (n+m) ∈ 𝔽 → 𝕋 M (n+m) = 𝕋 M n + 𝕋 M m:=
  assume m,
  begin
    unfold Z74, 
    rw comprehension,
  end

def Zsubtraction:= setof(λ(p:M), p ∈ 𝔽 ∧ ( ∀(q r:M), q ∈ 𝔽  → r ∈ 𝔽 → q+p ∈ 𝔽 → q+p = r+p → q=r))

lemma Zsubtraction_members: ∀ (p:M), p ∈ Zsubtraction M ↔ 
 p ∈ 𝔽 ∧  ∀(q r:M), q ∈ 𝔽  → r ∈ 𝔽 → q+p ∈ 𝔽 → q+p = r+p → q=r:=
   assume p,
   begin
     unfold Zsubtraction,
     rw comprehension, 
   end
def Zdividebytwo:= setof(λ(m:M), m ∈ 𝔽 ∧ (m + m ∈ 𝔽 → ∀ (n:M), n ∈ 𝔽 → m+m=n+n → n=m))

lemma Zdividetbytwo_members: ∀(m:M), m ∈ Zdividebytwo M ↔ m ∈ 𝔽 ∧ (m + m ∈ 𝔽 → ∀ (n:M), n ∈ 𝔽 → m+m=n+n → n=m):=
  assume m,
  begin
    unfold Zdividebytwo,
    rw comprehension, 
  end 

def ZsixpointeightD(m y:M):M := setof(λ (q:M), q∈ 𝔽 ∧ (y ≤ q → 𝕀 M m q = Λ))

lemma ZsixpointeightD_members(m y:M): ∀ (q:M), q ∈ ZsixpointeightD M  m y ↔ (q ∈ 𝔽 ∧ (y ≤ q → 𝕀 M m q = Λ)):=
  assume q,
  begin 
    unfold ZsixpointeightD,
    rw comprehension,
  end 

def Wssc_adjoin2(b c:M):M := setof(λ u, ∃(x y:M), u = ‹ x,y › ∧ y = (x ∪ (single c)) ∧ x ∈ SSC b)

lemma Wssc_adjoin2_members(b c:M): ∀(u:M), u ∈ Wssc_adjoin2 M b c ↔ 
∃(x y:M), u = ‹ x,y › ∧ y = (x ∪ (single c)) ∧ x ∈ SSC b :=
  assume u,
  begin
    unfold Wssc_adjoin2,
    rw comprehension,
  end 

def W_finiteDNS:= setof(λ (B:M), B ∈ FINITE M ∧ ∀ (P:M), ((∀ (x:M),(x ∈ B → ¬¬ x ∈ P)) → ¬¬ ∀ (x:M), x ∈ B → x ∈ P))

lemma W_finiteDNS_members: ∀(B:M), B ∈ W_finiteDNS M  ↔  B ∈ FINITE M ∧ ∀ (P:M),((∀ (x:M),(x ∈ B → ¬¬ x ∈ P)) → ¬¬ ∀ (x:M), x ∈ B → x ∈ P):=
  assume B,
  begin
    unfold W_finiteDNS, 
    rw comprehension,
  end

def W_notnotfinite(X:M):= setof(λ(B:M), B ∈ FINITE M ∧ ¬¬ ∃(Y:M), Y ⊆ X ∧ similar M B Y)

lemma W_notnotfinite_members(X:M): ∀ (B:M), B ∈ W_notnotfinite M X ↔  B ∈ FINITE M ∧ ¬¬ ∃(Y:M), Y ⊆ X ∧ similar M B Y:=
  assume B,
  begin
    unfold W_notnotfinite,
    rw comprehension,
  end 

def Winfiniteimpliesnotfinite:= setof(λ(X:M), X ∈ FINITE M ∧ ∀ (Y:M), Y ⊆ X → similar M X Y → X=Y)

lemma Winfiniteimpliesnotfinite_members: ∀ (X:M), X ∈ Winfiniteimpliesnotfinite M ↔ X ∈ FINITE M ∧   ∀ (Y:M), Y ⊆ X → similar M X Y → X=Y:=
  assume x,
  begin
    unfold Winfiniteimpliesnotfinite, 
    rw comprehension,  
  end 

def ZTheorem3:M := setof(λ (x:M), x ∈ 𝔽 ∧ ∃ p, p ∈ 𝔽 ∧ 𝕋 M p = x)

lemma ZTheorem3_members: ∀(x:M), x ∈ ZTheorem3 M ↔ x ∈ 𝔽 ∧ ∃ p, p ∈ 𝔽 ∧ 𝕋 M p = x:=
  assume x,
  begin 
    unfold ZTheorem3,
    rw comprehension,
  end

def ZTorder:M := setof(λ (n:M), n ∈ 𝔽 ∧ ∀ (m:M), m ∈ 𝔽  → n < m → 𝕋 M n < 𝕋 M m)

lemma ZTorder_members: ∀ (n:M), n ∈ ZTorder M ↔ n ∈ 𝔽 ∧ ∀ (m:M), m ∈ 𝔽  → n < m → 𝕋 M n < 𝕋 M m:=
  begin
    intro n, 
    unfold ZTorder,
    rw comprehension,
  end 

def 𝕁(m:M):M := setof(λ (x:M), x ∈ 𝔽 ∧ x < m)
def Jbar(m:M):M := setof(λ (x:M), x ∈ 𝔽 ∧ x ≤ m)

lemma J_members: ∀ (m x:M), x ∈ 𝕁 M (m) ↔ x ∈ 𝔽 ∧ x < m:=
  assume m x,
  begin
    unfold 𝕁,
    rewrite comprehension, 
  end

lemma Jbar_members: ∀ (m x:M), x ∈ Jbar M (m) ↔ x ∈ 𝔽 ∧ x ≤  m:=
  assume m x,
  begin
    unfold Jbar,
    rewrite comprehension, 
  end

def ZIsuccessor:= setof(λ (y:M), y ∈ 𝔽 ∧ ∀ (m:M),m ∈ 𝔽 → exp M m ∈ 𝔽 →  (∃ (u:M), u ∈ 𝕊 y) → 𝕀 M m (𝕊 y) = 𝕀 M (exp M m) y)

lemma ZIsuccessor_members: ∀(y:M), y ∈ ZIsuccessor M ↔ 
y ∈ 𝔽 ∧ ∀ (m:M),m ∈ 𝔽 → exp M m ∈ 𝔽 →  (∃ (u:M), u ∈ 𝕊 y) → 𝕀 M m (𝕊 y) = 𝕀 M (exp M m) y:=
  assume y,
  begin
    unfold ZIsuccessor,
    rw comprehension,
  end 

def Zexponeone:= setof(λ (n:M), n ∈ 𝔽 ∧ ((∃ (u:M), u ∈ exp M n) → ∀ (m:M), m ∈ 𝔽 → exp M n = exp M m → n = m))

lemma Zexponeone_members: ∀(n:M), n∈ Zexponeone M ↔n ∈ 𝔽 ∧ ((∃ (u:M), u ∈ exp M n) → ∀ (m:M), m ∈ 𝔽 → exp M n = exp M m → n = m):=
  assume n,
  begin
    unfold Zexponeone,
    rw comprehension,
  end

def Z_orderbyaddition:= setof(λ (q:M), q ∈ 𝔽 ∧ ( ∀ (p:M), p ∈ 𝔽 → (p ≤ q ↔  ∃(k:M), k ∈ 𝔽 ∧ p + k = q)))

lemma Z_orderbyaddition_members: ∀ (q:M), q ∈ Z_orderbyaddition M ↔ q ∈ 𝔽 ∧ ( ∀ (p:M), p ∈ 𝔽 → ( p ≤ q ↔  ∃(k:M), k ∈ 𝔽 ∧ p + k = q)):=
  assume q,
  begin
    unfold Z_orderbyaddition,
    rw comprehension,
  end 

def WJ1:= setof(λ(x:M), x ∈ FINITE M ∧ (¬ x = Λ → x ∈ SSC 𝔽 → ∃(y:M), y ∈ 𝔽 ∧ x ⊆ Jbar M y ∧ y ∈ x))

lemma WJ1_members: ∀ (x:M), x ∈ WJ1 M ↔ x ∈ FINITE M ∧ (¬ x = Λ → x ∈ SSC 𝔽 → ∃(y:M), y ∈ 𝔽 ∧ x ⊆ Jbar M y ∧ y ∈ x):=
  begin
    intro x,
    unfold WJ1,
    rw comprehension,
  end

def WJsim:= setof(λ(x:M), x ∈ FINITE M ∧ (x ∈ SSC(𝔽 ) → ¬(x = 𝔽 ) → ∃(m:M), m ∈ 𝔽 ∧ similar M x (𝕁 M m)))

lemma WJsim_members: ∀ (x:M), x ∈ WJsim M ↔ x ∈ FINITE M ∧ 
(x ∈ SSC(𝔽 ) → ¬(x = 𝔽 ) → ∃(m:M), m ∈ 𝔽 ∧ similar M x (𝕁 M m)):=
  begin
    intro x,
    unfold WJsim,
    rw comprehension,
  end 


lemma W38_members: Rel (W38 M)  ∧ ∀ (x y:M),  -- formula (33), line 612
( ‹ x,y › ∈ W38 M ↔ ∃ z:M, (x = (single z) ∧ y = USC z)):=
  begin
    unfold W38,
    rw Rel_definition,
    split,
    { intros z h,
      rw comprehension at h,
      cases h with u h2,
      use single u, use USC u,
      exact h2, 
    },
    {
      intros x y,
      rw comprehension,
      split,
      {
        intro h3,
        cases h3 with z h4,
        rw ordered_pair_equality at h4,
        cases h4 with h5 h6,
        use z,
        exact ⟨ h5, h6⟩,
      },
      {
        intro h3,
        cases h3 with z h4,
        use z,
        rw ordered_pair_equality,
        exact h4, 
      }
    },
  end

lemma Z2_members: ∀ (κ:M), κ ∈ Z2 M ↔ κ ∈ 𝔽 ∧ ∀ (μ:M),   μ ∈ 𝔽 → 
((κ < μ ∨ κ = μ ∨ μ < κ) ∧ (¬ ( κ < μ ∧ μ < κ ))):=
  assume κ,
  begin
    unfold Z2,
    rw comprehension,
  end 

def Zfinitehelper:= setof(λ(n:M), n ∈ 𝔽 ∧  ∀ (m:M), ( m ∈ 𝔽 → n = Nc M (Φ M m) →  Φ M (𝕋 M m) ∈ FINITE M → ¬¬ ( Nc M (Φ M (𝕋 M m)) = 𝕋 M n+ one ∨ Nc M (Φ M (𝕋 M m)) = 𝕋 M n+ two )))

lemma Zfinitehelper_members: ∀(n:M), n ∈ Zfinitehelper M ↔ 
 n ∈ 𝔽 ∧  ∀ (m:M), m ∈ 𝔽 → n = Nc M (Φ M m) → Φ M (𝕋 M m) ∈ FINITE M → 
  ¬¬ (
  Nc M (Φ M (𝕋 M m)) = 𝕋 M n+ one ∨ Nc M (Φ M (𝕋 M m)) = 𝕋 M n+ two
  ):=
  assume n,
  begin
    unfold Zfinitehelper,
    rw comprehension,
  end 

def ZsixpointeightDown:M := setof(λ(y:M), y ∈ 𝔽 ∧ ∀ (m x:M), m ∈ 𝔽 → x ∈ 𝔽  → (∃ (u:M), u ∈ 𝕀 M m y) → x ≤ y → ∃ (u:M), (u ∈ 𝕀 M m x) ) 

lemma ZsixpointeightDown_members: ∀(y :M), y ∈ ZsixpointeightDown M ↔ y ∈ 𝔽 ∧ ∀ (m x:M), m ∈ 𝔽 → x ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y) → x ≤ y → ∃ (u:M), (u ∈ 𝕀 M m x):=
  assume y,
  begin 
    unfold ZsixpointeightDown,
    rw comprehension, 
  end 

def ZIinF(m:M):= setof(λ (y:M), y ∈ 𝔽 ∧ (m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽))

lemma ZIinF_members(m:M): ∀(y:M), y ∈ ZIinF M m ↔ y ∈ 𝔽 ∧ (m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽):=
  assume y,
  begin
    unfold ZIinF,
    rw comprehension, 
  end

def Zsixpointfour(m:M):M := setof(λ (y:M), y ∈ 𝔽 ∧ (𝕀 M m y ∈ 𝔽 →  m ≤ 𝕀 M m y ))

lemma Zsixpointfour_members(m:M): ∀ (y:M),  y ∈ Zsixpointfour M m ↔  y ∈ 𝔽 ∧  (𝕀 M m y ∈ 𝔽  →  m ≤ 𝕀 M m y):=
  assume y,
  begin
    unfold Zsixpointfour,
    rw comprehension,
  end 

lemma W23_members: ∀ (x:M), x ∈ W23 M ↔  (x∈ FINITE M ∧ Nc M x ∈ 𝔽):=
  assume x,
  begin
    unfold W23, 
    rw comprehension, 
  end 

lemma Nc_members: ∀(x u:M), u ∈ Nc M x ↔ similar M u x :=
  assume x u,
  begin
    unfold Nc, 
    rw comprehension, 
  end

lemma Z20_members: ∀ κ: M,( κ ∈ Z20 M ↔ ∀ (x y:M),(x∈ κ → y ∈ κ → similar M x y)):=
  assume κ,
  begin
    unfold Z20,
    rw comprehension, 
  end

lemma Z19_members: ∀ κ:M, (κ ∈ Z19 M ↔ κ ∈ 𝔽 ∧ ∀ (x y:M), x ∈ κ → similar M x y → y ∈ κ):=
  assume κ,
  begin
    unfold Z19,
    rw comprehension, 
  end

lemma W9_members: ∀ x: M,(x ∈ W9 M ↔ x ∈ FINITE M ∧  ∀ y,(  (similar M y x) → y ∈ FINITE M) ):=
  assume x,
  begin
    split,
      {  
        unfold W9, 
        intro h,
        rw  comprehension   at h, 
        exact h, 
      },
      { unfold W9, 
        intro h, 
        rw  comprehension ,
        exact h, 
      }
  end

lemma W15_members: ∀ x:M,(x ∈ W15 M ↔ x ∈ FINITE M ∧ ∀ y, (y ⊆ x → (similar M x y) → x=y )):=
  assume x,
  begin
    split,
      {  
        unfold W15, 
        intro h,
        rw  comprehension  at h, 
        exact h, 
      },
      { unfold W15, 
        intro h, 
        rw  comprehension,
        exact h,  
      }
  end 

lemma successor_members: ∀(u y:M), (y ∈ 𝕊 u ↔   ∃ x a,(x ∈ u ∧ ¬ a ∈ x ∧ y = (x ∪ (single a)))) :=
  assume x y,
  begin
    rw succ_definition,
    rw comprehension, 
  end 

def Z_Jfinite:= setof(λ (y:M), y ∈ 𝔽 ∧ 𝕁 M y ∈ FINITE M)

lemma Z_Jfinite_members: ∀ (y:M), y ∈ Z_Jfinite M ↔ y ∈ 𝔽 ∧ 𝕁 M y ∈ FINITE M:=
  assume y,
  begin
    unfold Z_Jfinite,
    rw comprehension,
  end 

def Z_towerstrictlyincreasing:= setof(λ (y:M), y ∈ 𝔽 ∧ ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y < 𝕀 M m y )

lemma Z_towerstrictlyincreasing_members: ∀ (y:M), y ∈ Z_towerstrictlyincreasing M ↔ 
 y ∈ 𝔽 ∧ ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y < 𝕀 M m y  :=
  assume y,
  begin
    unfold Z_towerstrictlyincreasing,
    rw comprehension, 
  end

def Z_Iorder:= setof(λ (y:M),  y ∈ 𝔽 ∧ ( ∀ (x m:M), x ∈ 𝔽 → m ∈ 𝔽 → 𝕀 M m y ∈ 𝔽 → x < y →  𝕀 M m x < 𝕀 M m y))

lemma Z_Iorder_members: ∀ (y:M), y ∈ Z_Iorder M ↔
 y ∈ 𝔽 ∧ ( ∀ (x m:M), x ∈ 𝔽 → m ∈ 𝔽 → 𝕀 M m y ∈ 𝔽 → x < y →  𝕀 M m x < 𝕀 M m y):=
  assume y,
  begin
    unfold Z_Iorder,
    rw comprehension, 
  end

def W_finitemaximal:= setof(λ(x:M), x ∈ FINITE M ∧ (x ⊆ 𝔽  →  ¬ (x = Λ ) → ∃ (m:M), (m ∈ x ∧ ∀ (t:M),  t∈ x → t ≤ m)))

lemma W_finitemaximal_members: ∀(x:M), x ∈ W_finitemaximal M ↔  x ∈ FINITE M ∧ ( x ⊆ 𝔽  →  ¬ (x = Λ )→ ∃ (m:M), (m ∈ x ∧ ∀ (t:M), t∈ x → t ≤ m)):=
  assume x,
  begin
    unfold W_finitemaximal,
    rw comprehension,
  end

def Z_zeroorsuccessorH:= setof(λ (x:M), x ∈ ℍ ∧ (x = zero ∨ ∃ (u:M), u ∈ ℍ ∧  𝕊 u = x))

lemma Z_zeroorsuccessorH_members: ∀ (x:M), x∈ Z_zeroorsuccessorH M ↔
x ∈ ℍ ∧ (x = zero ∨ ∃ (u:M), u ∈ ℍ ∧ 𝕊 u = x) :=
  assume x,
  begin
    unfold Z_zeroorsuccessorH,
    rw comprehension,
  end

def Z_doublecomplementF:= setof(λ(x:M), x ∈ ℍ ∧ ¬¬ x ∈ 𝔽 )

lemma Z_doublecomplementF_members: ∀ (x:M), x ∈ Z_doublecomplementF M ↔
x ∈ ℍ ∧ ¬¬ x ∈ 𝔽:=
  assume x,
  begin
    unfold Z_doublecomplementF,
    rw comprehension,
  end

def Z_Hdecidable:= setof(λ (x:M), x ∈ ℍ ∧ ∀ (y:M), y ∈ ℍ → x = y ∨ ¬(x=y))

lemma Z_Hdecidable_members: ∀ (x:M), x ∈ Z_Hdecidable M ↔ x ∈ ℍ ∧ ∀ (y:M), y ∈ ℍ → x = y ∨ ¬(x=y):=
  assume x,
  begin
    unfold Z_Hdecidable,
    rw comprehension,
  end 

def Z_emptynotinH:= setof(λ (x:M), x ∈ ℍ ∧ ¬ x = Λ )

lemma Z_emptynotinH_members: ∀ (x:M), x ∈ Z_emptynotinH M ↔ x ∈ ℍ ∧ ¬ x = Λ :=
  assume x,
  begin
    unfold Z_emptynotinH,
    rw comprehension,
  end

def Z_inhabitedHisF:= setof(λ (x:M), x ∈ ℍ ∧ ((∃ (u:M), u ∈ x) → x ∈ 𝔽))

lemma Z_inhabitedHisF_members: ∀ (x:M), x ∈ Z_inhabitedHisF M ↔
  x ∈ ℍ ∧ ((∃ (u:M), u ∈ x) → x ∈ 𝔽):=
  assume x,
  begin
    unfold Z_inhabitedHisF,
    rw comprehension, 
  end

def Z_Hinfinite1(m:M):M := setof(λ (y:M), y ∈ ℍ ∧ ¬¬ 𝕀 M m y ∈ ℍ )

lemma Z_Hinfinite1_members(m:M): ∀ (y:M), y ∈ Z_Hinfinite1 M m ↔ y ∈ ℍ ∧ ¬¬ 𝕀 M m y ∈ ℍ:=
  assume y,
  begin
    unfold Z_Hinfinite1, 
    rw comprehension,
  end 

def Z_boundedDNS(P:M):M := setof(λ (y:M), y ∈ 𝔽 ∧ ((∀ (x:M), x∈ 𝔽 → x < y → ¬¬ x ∈ P) → (¬¬ ∀ (x:M), x ∈ 𝔽 → x < y →  x ∈ P)  ))

lemma Z_boundedDNS_members(P:M): ∀ (y:M), y ∈ Z_boundedDNS M P ↔ y ∈ 𝔽 ∧ 
((∀ (x:M), x∈ 𝔽 → x < y → ¬¬ x ∈ P) → (¬¬ ∀ (x:M), x ∈ 𝔽 → x < y →  x ∈ P))
:=
  assume y,
  begin
    unfold Z_boundedDNS,
    rw comprehension, 
  end 

def Egraph:M := setof(λ (u:M), (∃ (x y:M), u = ‹ x,y›)  ∧ ∀ (w:M),‹ zero,one› ∈ w →  (∀ (x y:M), ‹ x,y › ∈ w → (¬ (𝕊 x = Λ ))→ ‹ 𝕊 x, y+y› ∈ w)  → u ∈ w)

lemma Egraph_members: ∀(u:M), u ∈ Egraph M ↔ (∃ (x y:M), u = ‹ x,y›)  ∧ ∀ (w:M),
‹ zero,one› ∈ w → (∀ (x y:M),  ‹ x,y › ∈ w → (¬ (𝕊 x = Λ )) → ‹ 𝕊 x, y+y› ∈ w)  → u ∈ w:= 
  begin
    intro u, 
    unfold Egraph, 
    rw comprehension,  
  end

def 𝔼(x:M) := setof(λ (p:M), ∃ (y:M), ‹ x,y › ∈ Egraph M ∧ p ∈ y) 

lemma E_members: ∀ (x p:M), p ∈ 𝔼 M x ↔ ∃ (y:M), ‹ x,y › ∈ Egraph M ∧ p ∈ y :=
  assume x p,
  begin
    unfold 𝔼,
    rw comprehension, 
  end 

def Z_Emaps1 := setof(λ(x:M), x ∈ ℍ ∧  ∃ (y:M), ‹ x,y› ∈ Egraph M) 

lemma Z_Emaps1_members: ∀ (x:M), x ∈ Z_Emaps1 M ↔  x ∈ ℍ ∧  ∃ (y:M), ‹ x,y› ∈ Egraph M:=
  assume x,
  begin
    unfold Z_Emaps1,
    rw comprehension,
  end 

def Z_Emaps2:= setof(λ(x:M), x ∈ ℍ ∧ ∀ (y u:M), ‹ x,u› ∈ Egraph M → ‹ x,y › ∈ Egraph M → y = u)

lemma Z_Emaps2_members: ∀ (x:M), x ∈ Z_Emaps2 M ↔ x ∈ ℍ ∧ ∀ (y u:M), ‹ x,u› ∈ Egraph M → ‹ x,y › ∈ Egraph M → y = u:=
  assume x,
  begin
    unfold Z_Emaps2,
    rw comprehension,
  end

def Z_nonemptysum:= setof( λ (y:M), y∈ ℍ  ∧  ∀ (x:M), x ∈ ℍ → ¬ x + y = Λ → x + y ∈ ℍ)

lemma Z_nonemptysum_members: ∀ (y:M), y ∈ Z_nonemptysum M ↔ 
y∈ ℍ  ∧  ∀ (x:M), x ∈ ℍ → ¬ x + y = Λ → x + y ∈ ℍ:=
  assume y,
  begin
    unfold Z_nonemptysum,
    rw comprehension, 
  end

def W_Ehelper2:= setof(λ(u:M), ∃ (x y:M), u = ‹ x,y› ∧ (¬ (x = Λ ) → x ∈ ℍ ) ∧ (¬ (y = Λ )→ y ∈ ℍ ))

lemma W_Ehelper2_members: ∀ (u:M), u ∈ W_Ehelper2 M ↔  ∃ (x y:M), u = ‹ x,y› ∧
(¬ (x = Λ ) → x ∈ ℍ ) ∧ (¬ (y = Λ )→ y ∈ ℍ ):=
  assume u,
  begin
    unfold W_Ehelper2,
    rw comprehension,
  end 

def W_maps2(x y:M):= setof(λ (u:M),  ∃ (s t:M), u = ‹ s,t› ∧ ‹s,t› ∈ Egraph M ∧ (¬ (s = Λ ) → s ∈ ℍ) ∧ (s = 𝕊 x → t = y+y))

lemma W_maps2_members(x y:M)  : ∀(u:M), u ∈ W_maps2 M x y ↔ 
∃ (s t:M), u = ‹ s,t› ∧ ‹s,t› ∈ (Egraph M) ∧ (¬ (s = Λ ) → s ∈ ℍ) ∧ (s = 𝕊 x → t = y+y):=
  assume u,
  begin
    unfold W_maps2,
    rw comprehension, 
  end

def Z_expH:= setof(λ (m:M), m ∈ ℍ ∧ ( ¬ (𝔼 M m = Λ) → 𝔼 M m ∈ ℍ) )

lemma Z_expH_members: ∀ (m:M), m ∈ Z_expH M ↔  m ∈ ℍ ∧ ( ¬ (𝔼 M m = Λ) → 𝔼 M m ∈ ℍ) :=
  assume m,
  begin
    unfold Z_expH,
    rw comprehension,
  end 

def Z_Etoexp:= setof(λ (y:M), y ∈ ℍ ∧ ((∃ (u:M), u ∈ exp M y) → 𝔼 M y = exp M y))

lemma Z_Etoexp_members: ∀ (y:M), y ∈ Z_Etoexp M ↔ y ∈ ℍ ∧ ((∃ (u:M), u ∈ exp M y) → 𝔼 M y = exp M y):=
  assume y,
  begin
    unfold Z_Etoexp,
    rw comprehension,
  end 

def IEgraph:= setof(λ u, ∃ (x y z:M), u = triple  x y z  ∧ y ∈ ℍ   ∧ ∀ (Z:M),  (∀ (m:M), triple m zero m ∈ Z) ∧  ((∀ (m y z:M), triple m y z ∈ Z → (¬  𝕊 y = Λ ) →  triple m (𝕊 y) ( 𝔼  M z) ∈ Z)) → u ∈ Z)

lemma IEgraph_members1: Rel (IEgraph M):= 
  begin
    unfold Rel_definition, 
    intro u,
    unfold IEgraph,
    rw comprehension,
    intro h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    rw triple_definition at h5,
    use ‹ x, y ›, 
    use single (single z),
    exact h5, 
  end

lemma IEgraph_members2: ∀ (u:M), u ∈ IEgraph M → ∃ (x y z:M), u = triple x y z:=
  assume u,
  begin
    intro h,
    unfold IEgraph at h,
    rw comprehension at h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    use x, use y, use z, 
    exact h5, 
  end 

lemma IEgraph_members: ∀ (x y z:M), (triple x y z ∈ IEgraph M ↔ y ∈ ℍ  ∧ 
∀ (Z:M), 
      (∀ (m:M), triple m zero m ∈ Z) ∧  
      (∀ (m y z:M), triple m y z ∈ Z →  (¬  𝕊 y = Λ ) → triple m (𝕊 y) ( 𝔼  M z) ∈ Z)
      → triple x y z ∈ Z ):=
  assume x y z, 
  begin
    unfold IEgraph,
    rw comprehension, 
    split,
    {
      intro h,
      cases h with p h2,
      cases h2 with q h3,
      cases h3 with r h4,
      cases h4 with h5 h6,
      rw triple_equality M at h5,
      rcases h5 with ⟨ h7, h8, h9⟩,
      rw h7 at *,
      rw h8 at *,
      rw h9 at *,
      exact h6,
    },
    {
      intro h,
      use x, use y, use z, 
      rw triple_equality,
      split,
      {
        exact ⟨ refl x, refl y, refl z⟩, 
      },
      {
        exact h, 
      }
    }
  end 

def Z_IEgraph:M := setof(λ y,  y ∈ ℍ  ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ IEgraph M)
def Z_IEgraph2:M := setof(λ y, y ∈ ℍ   ∧ ∀ (x z w:M), (triple x y z ∈ IEgraph M 
∧ triple x y w ∈ IEgraph M → z = w))
def Z_IE_defined:M := setof(λ y, y ∈ ℍ  ∧ ∀(m:M), ∃(z:M), triple m y z ∈ IEgraph M)
def Z_IE_singlevalued:M := setof(λ y, y ∈ ℍ   ∧ ∀ (m z w:M), triple m y z ∈ IEgraph M → triple m y w ∈ IEgraph M → z = w )
def W181:M := setof(λ u, ∃(m y z:M), u = triple m y z ∧ triple m y z ∈ IEgraph M ∧ ( (y=zero ∧ z = m)  ∨ ∃ (p w:M), y = 𝕊 p ∧ (¬ (y = Λ )) ∧ triple m p w ∈ IEgraph M ∧ z = 𝔼  M w))
def Z182:M := setof(λ y, y ∈ ℍ ∧ ∀ (m z w:M), triple m y z ∈ IEgraph M → triple m y w ∈ IEgraph M → z = w)

lemma Z182_members: ∀ (y:M), y ∈ Z182 M ↔ y ∈ ℍ ∧ ∀ (m z w:M), triple m y z ∈ IEgraph M → triple m y w ∈ IEgraph M → z = w:=
  assume y,
  begin
    unfold Z182,
    rw comprehension,
  end 

lemma W181_members: ∀ (u:M), u ∈ W181 M ↔ 
∃(m y z:M), u = triple m y z ∧ triple m y z ∈ IEgraph M ∧
( (y=zero ∧ z = m)  ∨ ∃ (u w:M), y = 𝕊 u ∧ (¬( y = Λ)) ∧ triple m u w ∈ IEgraph M ∧ z = 𝔼 M w):=
  assume u,
    begin
      unfold W181,
      rw comprehension, 
    end

lemma Z_IEgraph_members: ∀(y:M), y ∈ Z_IEgraph M ↔ y ∈ ℍ  ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ IEgraph M:=
  assume y,
  begin
    unfold Z_IEgraph,
    rw comprehension, 
  end 

lemma Z_IEgraph2_members: ∀ (y:M), y ∈ Z_IEgraph2 M ↔ 
y ∈ ℍ   ∧ ∀ (x z w:M), (triple x y z ∈ IEgraph M 
∧ triple x y w ∈ IEgraph M → z = w) :=
 assume y,
  begin
    unfold Z_IEgraph2,
    rw comprehension, 
  end 

lemma Z_IE_defined_members: ∀(y:M), y ∈ Z_IE_defined M ↔
  y ∈ ℍ  ∧ ∀(m:M), ∃(z:M), triple m y z ∈ IEgraph M:=
  assume y,
  begin
    unfold Z_IE_defined,
    rw comprehension,
  end 

lemma Z_IE_singlevalued_members: ∀(y:M), y ∈ Z_IE_singlevalued M ↔
 y ∈ ℍ  ∧ ∀ (m z w:M), triple m y z ∈ IEgraph M → triple m y w ∈ IEgraph M → z = w :=
  assume y,
  begin
    unfold Z_IE_singlevalued,
    rw comprehension,
  end 

def 𝕀𝔼 (m y:M):= setof(λ u,∃ (z:M), triple m y z ∈ IEgraph M ∧ u ∈ z)


lemma IE_members: ∀ (m y :M), u ∈ 𝕀𝔼  M m y  ↔ ∃(z:M), triple m y z ∈ IEgraph M ∧ u ∈ z:=
  assume z m,
  begin
    unfold 𝕀𝔼,
    rw comprehension,      
  end 

def Z183:M := setof(λ y, y ∈ ℍ  ∧ ∀ (m z:M), triple m y z ∈ IEgraph M ↔ z = 𝕀𝔼  M m y)

lemma Z183_members: ∀ (y:M), y ∈ Z183 M ↔ y ∈ ℍ  ∧ ∀ (m z:M), triple m y z ∈ IEgraph M ↔ z = 𝕀𝔼 M m y:=
  assume y,
  begin
    unfold Z183,
    rw comprehension, 
  end 

def Z186(m:M):M := setof(λ y, y ∈ ℍ  ∧  ((¬ (𝕀𝔼  M m y = Λ )) → 𝕀𝔼  M m y ∈ ℍ ))
def Z187(m:M):M := setof(λ y, y ∈ ℍ  ∧  ( m ∈ ℍ  →  (¬ ( 𝕀𝔼  M m y = Λ )) → y ≤ 𝕀𝔼  M m y))

lemma Z186_members : ∀(m y:M), y ∈ Z186 M m ↔ y ∈ ℍ  ∧ (( ¬ ( 𝕀𝔼  M m y = Λ )) → 𝕀𝔼  M m y ∈ ℍ ) :=
  assume m y,
  begin
    unfold Z186,
    rw comprehension, 
  end

lemma Z187_members : ∀(m y:M), y ∈ Z187 M m ↔ y ∈ ℍ  ∧ ( m ∈ ℍ →  (¬(  𝕀𝔼  M m y = Λ )) → y ≤ 𝕀𝔼  M m y) :=
  assume m y,
  begin
    unfold Z187,
    rw comprehension, 
  end

def Z_IsubsetIE := setof(λ (y:M), y ∈ ℍ  ∧ ( ∀ (m:M), m ∈ 𝔽 →  (∃(u:M), u ∈ 𝕀 M m y)→ 𝕀 M m y = 𝕀𝔼 M m y))

lemma Z_IsubsetIE_members : ∀(y:M), y ∈ Z_IsubsetIE M ↔ y ∈ ℍ ∧ (∀ (m:M), m ∈ 𝔽 →  (∃(u:M), u ∈ 𝕀 M m y)→ 𝕀 M m y = 𝕀𝔼 M m y):=
  assume y,
  begin
    unfold Z_IsubsetIE,
    rw comprehension,
  end 

def Z_IshadowsubsetIE(m:M):= setof(λ(y:M), y ∈ ℍ ∧ ( ¬¬ 𝕀𝔼 M m y = 𝕀 M m y))

lemma Z_IshadowsubsetIE_members(m:M): ∀ (y:M), y∈ Z_IshadowsubsetIE M m↔  y ∈ ℍ ∧ ( ¬¬ 𝕀𝔼 M m y = 𝕀 M m y):=
  assume y, 
  begin
    unfold Z_IshadowsubsetIE,
    rw comprehension,
  end

def Z_PhiH(m:M):= setof(λ(y:M), y ∈ ℍ ∧   𝕀𝔼  M m y ∈ ℍ)

lemma Z_PhiH_members(m:M): ∀ (y:M), y ∈ Z_PhiH M m ↔ y ∈ ℍ ∧   𝕀𝔼  M m y ∈ ℍ:=
  assume y, 
  begin
    unfold Z_PhiH,
    rw comprehension,
  end 

def Z_IEnonzero(m:M):= setof(λ (y:M), y ∈ ℍ ∧  ¬ 𝕀𝔼  M m y  = zero )

lemma Z_IEnonzero_members(m:M): ∀ (y:M), y ∈ Z_IEnonzero M m↔ y ∈ ℍ ∧   ¬ 𝕀𝔼  M m y  = zero:=
  assume y,
  begin
    unfold Z_IEnonzero,
    rw comprehension,
  end

def fH (m:M):= setof(λ(u:M), ∃(y z:M), y ∈ ℍ ∧ z = 𝕀𝔼 M m y ∧ u = ‹ y,z ›)

lemma fH_members(m:M): ∀(u:M), u ∈ fH M m ↔  ∃(y z:M), y ∈ ℍ ∧ z = 𝕀𝔼 M m y ∧ u = ‹ y,z ›:=
  assume u,
  begin
    unfold fH,
    rw comprehension, 
  end

def JbarH(m:M) := setof(λ (x:M), x ∈ ℍ ∧ x ≤ℍ m)

lemma JbarH_members(m:M): ∀ (x:M), x ∈ JbarH M m ↔ x ∈ ℍ ∧ x ≤ℍ m:=
  assume x,
  begin
    unfold JbarH,
    rw comprehension,
  end

def Z_JbarHfinite:= setof(λ (m:M), m ∈ ℍ ∧ JbarH M m ∈ FINITE M)

lemma Z_JbarHfinite_members: ∀ (m:M), m ∈ Z_JbarHfinite M ↔ m ∈ ℍ ∧ JbarH M m ∈ FINITE M:=
  assume m,
  begin
    unfold Z_JbarHfinite,
    rw comprehension,
  end 

def Z_successorHnotempty(m:M):= setof(λ (x:M), x ∈ ℍ ∧  x ≤ℍ m)

lemma Z_successorHnotempty_members(m:M): ∀ (x:M), x ∈ Z_successorHnotempty M m ↔ x ∈ ℍ ∧ x ≤ℍ m:=
  assume x,
  begin
    unfold Z_successorHnotempty,
    rw comprehension,
  end 

def Z_successorHclosed:= setof(λ (x:M), x ∈ ℍ ∧ 𝕊 x ∈ ℍ )

lemma Z_successorHclosed_members: ∀ (x:M), x ∈ Z_successorHclosed M ↔ x ∈ ℍ ∧ 𝕊 x ∈ ℍ :=
  assume x,
  begin
    unfold Z_successorHclosed,
    rw comprehension,
  end 

def Z_additionclosureH:= setof(λ(y:M), y ∈ ℍ ∧ ∀ (x:M), x ∈ ℍ → x + y ∈ ℍ )

lemma Z_additionclosureH_members: ∀ (y:M), y ∈ Z_additionclosureH M ↔ y ∈ ℍ ∧ ∀ (x:M), x ∈ ℍ → x + y ∈ ℍ :=
  assume y,
  begin
    unfold Z_additionclosureH,
    rw comprehension, 
  end

def Z_FequalsH:= setof(λ (m:M), m ∈ 𝔽 ∧ (𝕊 m ∈ 𝔽 ∧ ∃ (k:M), k ∈ ℍ ∧  JbarH M k ∈ 𝕊 m))

lemma Z_FequalsH_members : ∀ (m:M), m ∈ Z_FequalsH M ↔ m ∈ 𝔽 ∧ (𝕊 m ∈ 𝔽 ∧ ∃ (k:M), k ∈ ℍ ∧  JbarH M k ∈ 𝕊 m):=
  assume m,
  begin
    unfold Z_FequalsH,
    rw comprehension,
  end 

lemma sym: ∀ (x y:M), x=y ↔ y=x:=
  assume x y,
  begin 
    split,
    {
      intro h,
      symmetry,
      exact h,
    },
    {
      intro h,
      symmetry,
      exact h, 
    }
  end

def W_finitehelper:=setof(λ (B:M), B ∈ FINITE M ∧  ∀ (A:M), A ∈ FINITE M → Nc M A = Nc M B → A ⊆ B → A = B)

lemma W_finitehelper_members: ∀ (B:M), B ∈ W_finitehelper M ↔
B ∈ FINITE M ∧  ∀ (A:M), A ∈ FINITE M → Nc M A = Nc M B → A ⊆ B → A = B:=
  assume B,
  begin
    unfold W_finitehelper,
    rw comprehension,
  end 

def lem_set (A:M):= setof(λ (t:M), (t ∈ A ∨ ¬ t ∈ A)) 
lemma lem_set_members(A:M): ∀ (t:M), t ∈ lem_set M A ↔  (t ∈ A ∨ ¬ t ∈ A):=
  begin
    intro t, 
    unfold lem_set, 
    rw comprehension,
  end 

def finitedns_helper (P c:M):= setof(λ (x:M), x ∈ P ∧ c ∈  P)

lemma finitedns_helper_members (P c:M): ∀ (x:M), (x ∈ finitedns_helper M P c ↔ x ∈ P ∧ c ∈ P):=
  assume x,
  begin
    unfold finitedns_helper,
    rw comprehension, 
  end

def Z_Tonto:= setof(λ(p:M), p ∈ 𝔽 ∧  ∀ (q:M), q ∈ 𝔽 →  p < 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ p = 𝕋 M r)

lemma Z_Tonto_members: ∀(p:M), p∈ Z_Tonto M ↔ p ∈ 𝔽 ∧  ∀ (q:M),q ∈ 𝔽 →  p < 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ p = 𝕋 M r:=
  assume p,
  begin
    unfold Z_Tonto,
    rw comprehension, 
  end

def Z_Tonto3:= setof(λ(p:M), p ∈ 𝔽 ∧  ∀ (q:M), q ∈ 𝔽 →  p < 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ p = 𝕋 M r ∧ r < q)

lemma Z_Tonto3_members: ∀(p:M), p∈ Z_Tonto3 M ↔ p ∈ 𝔽 ∧  ∀ (q:M),q ∈ 𝔽 →  p < 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ p = 𝕋 M r ∧ r < q:=
  assume p,
  begin
    unfold Z_Tonto3,
    rw comprehension, 
  end


def Z_expTconverse:= setof(λ(m:M), m ∈ 𝔽 ∧ ∀(n:M), n ∈ 𝔽 → exp M (𝕋 M m) = 𝕋 M n → n = exp M m)

lemma Z_expTconverse_members: ∀ (m:M), m ∈ Z_expTconverse M ↔  m ∈ 𝔽 ∧ ∀(n:M), n ∈ 𝔽 → exp M (𝕋 M m) = 𝕋 M n → n = exp M m :=
  assume m,
  begin
    unfold Z_expTconverse,
    rw comprehension,
  end

def SF := setof(λ(x:M), ∀(w:M),(zero ∈ w → (∀(u:M), u ∈ w → 𝕊 u ∈ w) → x ∈ w))

lemma SF_members: ∀ (x:M), x ∈ SF M ↔ ∀(w:M),(zero ∈ w → (∀(u:M), u ∈ w → 𝕊 u ∈ w) → x ∈ w):=
  assume x,
  begin
    unfold SF,
    rw comprehension,
  end 
  
def DC := setof(λ (m:M), ∀(u:M), u ∈ m → u ∈ DECIDABLE M ∧ ∀(v:M), v ∈  m ↔ similar M v u)

lemma DC_members: ∀ (m:M), m ∈ DC M ↔ ( ∀(u:M), u ∈ m → u ∈ DECIDABLE M ∧ ∀(v:M), v ∈  m ↔ similar M v u):=
  assume m,
  begin
    unfold DC,
    rw comprehension,
  end

def multiplication_graph:= setof(λ (v:M), ∃ (x y z:M),v = triple x y z ∧ ∀ (w:M), (∀(u:M), u ∈ SF M → triple u zero zero ∈ w ∧ triple zero u zero ∈ w) → (∀ (u v t:M), triple u v t ∈ w → triple u (𝕊 v) (t + u) ∈ w) → triple x y z ∈ w)

lemma multiplication_graph_members: ∀ (v:M), v ∈ multiplication_graph M ↔
 ∃ (x y z:M),v = triple x y z ∧ ∀ (w:M),
(∀(u:M), u ∈ SF M → triple u zero zero ∈ w ∧ triple zero u zero ∈ w) → 
(∀ (u v t:M), triple u v t ∈ w → triple  u (𝕊 v) (t +  u) ∈ w) → 
triple x y z ∈ w:=
  assume u,
  begin
    unfold multiplication_graph,
    rw comprehension, 
  end

def multiply (x y:M):M  := setof (λ (p:M), ∃(z:M), triple x y z ∈ multiplication_graph M ∧ p ∈ z)

instance Model.has_mul : has_mul M := ⟨multiply M⟩

lemma multiplication1: ∀ (x y:M), x*y = multiply M x y:=
  assume x y,
  begin
    unfold multiply,
    refl,
  end 

lemma multiplication_members2: ∀ (x y p:M), p ∈ x * y ↔
∃ (z:M), triple x y z ∈ multiplication_graph M ∧ p ∈ z:=
  assume x y p,
  begin
    rw multiplication1, 
    unfold multiply,
    rw comprehension, 
  end

def Z_zero_or_successor:= setof(λ(x:M), x ∈ SF M ∧ (x = zero ∨ ∃(u:M), u ∈ SF M ∧ 𝕊 u = x))

lemma Z_zero_or_successor_members: ∀ (x:M), x ∈ Z_zero_or_successor M ↔ 
x ∈ SF M ∧ (x = zero ∨ ∃(u:M), u ∈ SF M ∧ 𝕊 u = x):=
  assume x,
  begin
    unfold Z_zero_or_successor,
    rw comprehension, 
  end

def Z_additionSF:= setof(λ(y:M), y ∈ SF M ∧ ∀ (x:M), x ∈ SF M → x + y ∈ SF M)

lemma Z_additionSF_members: ∀ (y:M), y ∈ Z_additionSF M ↔
y ∈ SF M ∧ ∀ (x:M), x ∈ SF M → x + y ∈ SF M:=
  assume y,
  begin
    unfold Z_additionSF,
    rw comprehension, 
  end

def W_zero_or_successor:= setof(λ(t:M), t  ∈ multiplication_graph M ∧ ∃(x y z:M), t =triple x y z  ∧ (z = zero ∨ ∃ (p:M), z = 𝕊 p))

def W_zero_or_successor_members: ∀ (t:M), t ∈ W_zero_or_successor M ↔
 t  ∈ multiplication_graph M ∧ ∃(x y z:M), t =triple x y z  ∧
(z = zero ∨ ∃ (p:M), z = 𝕊 p):=
  assume t,
  begin
    unfold W_zero_or_successor,
    rw comprehension,
  end 

def W_multiplication3:= setof(λ(t:M),  t  ∈ multiplication_graph M ∧ ∃(x y z:M), t =triple x y z  ∧ (z = zero → x = zero ∨ y = zero) ∧ (¬ z = zero → ∃ (p q r:M), x = 𝕊 p ∧ y = 𝕊 q ∧ z = 𝕊 (r+p) ∧ triple x q r ∈ multiplication_graph M))

lemma W_multiplication3_members: ∀(t:M), t ∈ W_multiplication3 M ↔
t  ∈ multiplication_graph M ∧ ∃ (x y z:M), t =triple x y z  ∧
(z = zero → x = zero ∨ y = zero) ∧
(¬ z = zero → ∃ (p q r:M), x = 𝕊 p ∧ y = 𝕊 q ∧ z = 𝕊 (r+p) ∧ triple x q r ∈ multiplication_graph M):=
  assume t,
  begin 
    unfold W_multiplication3,
    rw comprehension, 
  end 

def Z_multiplication4:= setof(λ(y:M), y ∈ 𝔽 ∧  ∀ (x z t:M), triple x y z ∈ multiplication_graph M → triple x y t ∈ multiplication_graph M → z = t)

lemma Z_multiplication4_members: ∀ (y:M), y ∈ Z_multiplication4 M ↔
y ∈ 𝔽 ∧  ∀ (x z t:M), triple x y z ∈ multiplication_graph M→
triple x y t ∈ multiplication_graph M→ z = t :=
  assume y,
  begin
    unfold Z_multiplication4,
    rw comprehension, 
  end

def Z_multiplication4SF:= setof(λ(y:M), y ∈ SF M ∧  ∀ (x z t:M), triple x y z ∈ multiplication_graph M → triple x y t ∈ multiplication_graph M → z = t)

lemma Z_multiplication4SF_members: ∀ (y:M), y ∈ Z_multiplication4SF M ↔
y ∈ SF M ∧  ∀ (x z t:M), triple x y z ∈ multiplication_graph M→
triple x y t ∈ multiplication_graph M→ z = t :=
  assume y,
  begin
    unfold Z_multiplication4SF,
    rw comprehension, 
  end

def identityNF(x:M):= setof(λ (u:M), ∃(a:M), u = ‹ a,a › ∧ a ∈ x)

lemma identity_membersNF(x:M): ∀ (u:M), u ∈ identityNF M x ↔  ∃ (a:M), u = ‹ a,a › ∧ a ∈ x :=
  assume u,
  begin
    unfold identityNF,
    rw comprehension, 
  end

def W_multiplicationSF:= setof(λ(u:M), ∃ (x y z:M), u = triple x y z ∧ x ∈ SF M ∧ y ∈ SF M ∧ z ∈ SF M)

lemma W_multiplicationSF_members: ∀(u:M),u ∈ W_multiplicationSF M ↔ 
∃ (x y z:M), u = triple x y z ∧ x ∈ SF M ∧ y ∈ SF M ∧ z ∈ SF M:=
  assume u,
  begin
    unfold W_multiplicationSF,
    rw comprehension, 
  end 

def Z_multiplication2c := setof(λ (y:M), y∈ 𝔽  ∧ ∀ (u:M), triple u y zero ∈ multiplication_graph M → u = zero)

lemma Z_multiplication2c_members: ∀ (y:M), y∈ Z_multiplication2c M ↔ y∈ 𝔽  ∧ ∀ (u:M), triple u y zero ∈ multiplication_graph M → u = zero:=
  assume y,
  begin
    unfold Z_multiplication2c,
    rw comprehension,
  end

def Z_addstozero:= setof(λ(y:M), y ∈ SF M ∧  ∀(x:M), x ∈ SF M → x + y = zero → x = zero ∧ y = zero)

lemma Z_addstozero_members: ∀ (y:M), y ∈ Z_addstozero M ↔
y ∈ SF M ∧ ∀(x:M), x ∈ SF M → x + y = zero → x = zero ∧ y = zero:=
  assume y,
  begin
    unfold Z_addstozero,
    rw comprehension,
  end 

def W_multiplication3helper:= setof(λ(u:M), u ∈ multiplication_graph M ∧ ∀ (y z:M), u = triple zero y z → z = zero)

lemma W_multiplication3helper_members : ∀ (u:M), u ∈ W_multiplication3helper M ↔ 
u ∈ multiplication_graph M ∧ ∀ (y z:M), u = triple zero y z → z = zero:=
  assume u,
  begin
    unfold W_multiplication3helper,
    rw comprehension, 
  end 

def Z_inhabitedSF:= setof(λ(m:M), m ∈ SF M ∧ ((∃(u:M), u ∈ m) → m ∈ 𝔽 ))

lemma Z_inhabitedSF_members: ∀ (m:M), m ∈ Z_inhabitedSF M ↔ m ∈ SF M ∧ ((∃(u:M), u ∈ m) → m ∈ 𝔽 ):=
  assume m,
  begin
    unfold Z_inhabitedSF,
    rw comprehension,
  end 

def Z_multiplication5:= setof(λ(y:M), y ∈ 𝔽 ∧  ∀ (x :M), x ∈ 𝔽 → x*y ∈ SF M ∧ ∀ (z:M), z ∈ SF M → (triple x y z ∈ multiplication_graph M ↔ z = x * y ))

lemma Z_multiplication5_members: ∀ (y:M), y ∈ Z_multiplication5 M ↔ 
(y ∈ 𝔽 ∧  ∀ (x :M), x ∈ 𝔽 → 
x*y ∈ SF M ∧ ∀ (z:M), z ∈ SF M → (triple x y z ∈ multiplication_graph M ↔ z = x * y )):=
  assume u,
  begin
    unfold Z_multiplication5,
    rw comprehension,
  end

def Z_right_distributiveNF:= setof(λ(z:M), z ∈ 𝔽 ∧  ∀ (x y: M), x ∈ 𝔽 → y ∈ 𝔽 → (y+z)∈ 𝔽 → x * (y+z) = x * y + x * z )

lemma Z_right_distributiveNF_members: ∀ (z:M), z ∈ Z_right_distributiveNF M ↔
(z ∈ 𝔽 ∧  ∀ (x y: M), x ∈ 𝔽 → y ∈ 𝔽 → (y+z)∈ 𝔽 → 
x * (y+z) = x * y + x * z) :=
  assume z,
  begin
    unfold Z_right_distributiveNF,
    rw comprehension, 
  end

def Z_subtractionF:= setof(λ (u:M), u ∈ 𝔽 ∧  ∀(x:M), x ∈ SF M → x+u ∈ 𝔽 → x ∈ 𝔽 )

lemma Z_subtractionF_members: ∀ (u:M), u ∈ Z_subtractionF M ↔ 
u ∈ 𝔽 ∧  ∀(x:M), x ∈ SF M → x+u ∈ 𝔽 → x ∈ 𝔽 :=
  assume u,
  begin
    unfold Z_subtractionF,
    rw comprehension,
  end 

def Z_multiplication_associative:= setof(λ (z:M),z ∈ 𝔽 ∧  ∀ (x y:M), x ∈ 𝔽 →  y ∈ 𝔽 → x * y ∈ 𝔽 → y*z ∈ 𝔽 → x * (y* z) = (x * y) * z)

lemma Z_multiplication_associative_members: ∀ (z:M), z ∈ Z_multiplication_associative M ↔ 
z ∈ 𝔽 ∧ 
∀ (x y:M), x ∈ 𝔽 →  y ∈ 𝔽 → x * y ∈ 𝔽 →  y*z ∈ 𝔽 → x * (y* z) = (x * y) * z:=
  assume z,
  begin
    unfold Z_multiplication_associative,
    rw comprehension, 
  end

def Z_left_distributive := setof(λ(z:M),z ∈ 𝔽 ∧  ∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x + y ∈ 𝔽 → (x+y)*z = x * z + y * z )

lemma Z_left_distributive_members: ∀ (z:M), z ∈ Z_left_distributive M ↔
z ∈ 𝔽 ∧  ∀ (x y:M),
x ∈ 𝔽 → y ∈ 𝔽 → x + y ∈ 𝔽 → (x+y)*z = x * z + y * z:=
  assume z,
  begin
    unfold Z_left_distributive,
    rw comprehension,
  end 

def Z_multiplication_commutative:= setof(λ(y:M), y ∈ 𝔽 ∧ ∀ (x:M), x ∈ 𝔽 → x*y = y*x)

lemma Z_multiplication_commutative_members: ∀ (y:M), y ∈ Z_multiplication_commutative M ↔
 y ∈ 𝔽 ∧ ∀ (x:M), x ∈ 𝔽 → x*y = y*x:=
  assume y,
  begin
    unfold Z_multiplication_commutative,
    rw comprehension, 
  end 

def Z_one_mulNF:= setof(λ (x:M), x ∈ 𝔽 ∧ one *x = x)

lemma Z_one_mulNF_members: ∀ (x:M), x ∈ Z_one_mulNF M ↔ x ∈ 𝔽 ∧ one *x = x:=
  assume x,
  begin
    unfold Z_one_mulNF,
    rw comprehension,
  end 

def Z_exp_sum := setof(λ (q:M), q ∈ 𝔽 ∧  ∀ (p:M),p ∈ 𝔽  →p+q ∈ 𝔽 → exp M (p+q) ∈ 𝔽 → exp M p ∈ 𝔽 ∧ exp M q ∈ 𝔽 ∧ (exp M p)*(exp M q) ∈ 𝔽 ∧ exp M (p+q) = (exp M p)*(exp M q))

lemma Z_exp_sum_members: ∀ (q:M),q ∈ Z_exp_sum M ↔ 
q ∈ 𝔽 ∧  ∀ (p:M),p ∈ 𝔽 → p+q ∈ 𝔽 → exp M (p+q) ∈ 𝔽 → 
exp M p ∈ 𝔽 ∧ exp M q ∈ 𝔽 ∧ (exp M p)*(exp M q) ∈ 𝔽 ∧ 
exp M (p+q) = (exp M p)*(exp M q):=
  assume q,
  begin
    unfold Z_exp_sum,
    rw comprehension,
  end 

def Z_doubleexp:= setof(λ (p:M), p ∈ 𝔽 ∧ (exp M p = Λ → exp M (exp M (𝕋 M p)) = Λ))

lemma Z_doubleexp_members: ∀ (p:M), p ∈ Z_doubleexp M ↔ p ∈ 𝔽 ∧ (exp M p = Λ → exp M (exp M (𝕋 M p)) = Λ):=
  assume p,
  begin
    unfold Z_doubleexp,
    rw comprehension,
  end 

def Z_fivepointthree_converse:= setof(λ (b:M), b ∈ 𝔽 ∧  (∀ (a c:M), a ∈ 𝔽 → c ∈ 𝔽 →  𝕋 M a + 𝕋 M b  ∈ 𝔽 → 𝕋 M a + 𝕋 M b = 𝕋 M c → a + b = c))

lemma Z_fivepointthree_converse_members: ∀ (b:M), b ∈ Z_fivepointthree_converse M ↔ b ∈ 𝔽 ∧  (∀ (a c:M), a ∈ 𝔽 → c ∈ 𝔽 →  𝕋 M a + 𝕋 M b  ∈ 𝔽 → 𝕋 M a + 𝕋 M b = 𝕋 M c → a + b = c):=
  assume b,
  begin 
    unfold Z_fivepointthree_converse,
    rw comprehension, 
  end 

def W_finiteproduct_helper:= setof(λ (Y:M),  Y ∈ FINITE M ∧  (∀ (A a2:M), A ∈ DECIDABLE M → Y ⊆ A → single a2 × Y ∈ FINITE M))

lemma W_finiteproduct_helper_members: ∀ (Y:M), Y ∈ W_finiteproduct_helper M ↔ Y ∈ FINITE M ∧ ( ∀ (A a2:M), A ∈ DECIDABLE M → Y ⊆ A → single a2 × Y ∈ FINITE M):=
  assume Y,
  begin
    unfold W_finiteproduct_helper,
    rw comprehension, 
  end 

def W_productfinite:= setof(λ(X:M), X ∈ FINITE M ∧  ∀ (A Y:M), A ∈ DECIDABLE M → Y ∈ FINITE M → X ⊆ A → Y ⊆ A → X × Y ∈ FINITE M)

lemma W_productfinite_members: ∀ (X:M), X ∈ W_productfinite M ↔ X ∈ FINITE M ∧  ∀ (A Y:M), A ∈ DECIDABLE M → Y ∈ FINITE M → X ⊆ A → Y ⊆ A → X × Y ∈ FINITE M :=
  assume X,
  begin
    unfold W_productfinite,
    rw comprehension,
  end

def Z_quadraticgrowth:= setof(λ(k:M),  k ∈ 𝔽 ∧ (one < k → k*k ∈ 𝔽 → k < k*k))

lemma Z_quadraticgrowth_members: ∀ (k:M), k ∈ Z_quadraticgrowth M ↔  k ∈ 𝔽 ∧ ( one < k → k*k ∈ 𝔽 →  k < k*k) :=
  assume k,
  begin
    unfold Z_quadraticgrowth,
    rw comprehension,
  end 

def Z_expT_converse:= setof(λ(x:M),x ∈ 𝔽 ∧  ∀ (c:M), c ∈ 𝔽 → exp M (𝕋 M x) = 𝕋 M c → c = exp M x )

lemma Z_expT_converse_members: ∀ (x:M), x ∈ Z_expT_converse M ↔ x ∈ 𝔽 ∧ ∀ (c:M), c ∈ 𝔽 → exp M (𝕋 M x) = 𝕋 M c → c = exp M x :=
  assume x,
  begin
    unfold Z_expT_converse,
    rw comprehension,
  end 

def Z_Teven:= setof(λ (y:M), y ∈ 𝔽 ∧   ∀ (x:M), x ∈ 𝔽  → 𝕋 M x = y + y → y + y ∈ 𝔽  → ∃ (e:M), e ∈ 𝔽 ∧ x = e+e)

lemma Z_Teven_members: ∀ (y:M), y ∈ Z_Teven M ↔ y ∈ 𝔽 ∧  ∀ (x:M), x ∈ 𝔽  → 𝕋 M x = y + y → y + y ∈ 𝔽   → ∃ (e:M), e ∈ 𝔽 ∧ x = e+e:=
  assume x,
  begin
    unfold Z_Teven,
    rw comprehension, 
  end 

def Z_notnotmaxint:= setof(λ(x:M), ∃ (t:M), t ∈ 𝕊 x)

lemma Z_notnotmaxint_members: ∀ (x:M), x ∈ Z_notnotmaxint M ↔  ∃ (t:M), t ∈ 𝕊 x:=
  assume x,
  begin
    unfold Z_notnotmaxint,
    rw comprehension,
  end 

def W_finite_sscU(x U:M):= setof(λ (k:M), x ∈ k → x ∈ SSC U)

lemma W_finite_sscU_members(x U:M): ∀ (k:M), k ∈ W_finite_sscU M x U ↔ (x ∈ k → x ∈ SSC U):=
  assume k,
  begin
    unfold W_finite_sscU,
    rw comprehension,
  end

lemma FUNC_members: ∀ (f:M), f ∈ FUNC   ↔  ∀ (x y z:M), ‹ x,y › ∈ f → ‹ x,z› ∈ f → y = z:=
  assume f,
  begin
    rw FUNC_definition, 
    rw comprehension,
  end 

lemma Ap_members: ∀ (f x u:M), u ∈ Ap f x ↔ ∃ (y:M), ‹ x,y › ∈ f ∧ u ∈ y:=
  assume f x u,
  begin
    rw Ap_definition,
    rw comprehension,
  end

lemma Apdef: ∀ (f:M), f ∈ FUNC → ∀ (x y:M), ‹ x, y› ∈ f → y = Ap f x:=
  assume f,
  begin
    intros h x y,
    intro h3,
    rw full_extensionality,
    intro t,
    rw Ap_members,
    split,
    {
      intro h4,
      use y,
      exact ⟨ h3, h4⟩,
    },
    {
      intro h5,
      cases h5 with z h6,
      cases h6 with h7 h8,
      rw FUNC_members at h,
      have h9:= h x y z h3 h7,
      rw h9 at *,
      exact h8,
    }
end

def ChurchSuccessorGraph := setof(λ (u:M), ∃ (x:M), u = ‹ x, S x› )

lemma ChurchSuccessorGraph_members: ∀ (u:M), u ∈ ChurchSuccessorGraph M ↔  ∃ (x:M), u = ‹ x, S x›:=
  assume u,
  begin
    unfold ChurchSuccessorGraph,
    rw comprehension, 
  end 

def SG := setof(λ (u:M), ∃ (x:M), u = ‹ x, S x› ∧ x ∈ ℕℕ )

lemma SG_members: ∀ (u:M), u ∈ SG M ↔  ∃ (x:M), u = ‹ x, S x› ∧ x ∈ ℕℕ :=
  assume u,
  begin
    unfold SG,
    rw comprehension, 
  end

lemma ChurchSuccessor2: ∀ (z f:M), f ∈ FUNC → z ∈ FUNC → ∀(x w:M),
‹ x,w›  ∈ (Ap (S z) f) ↔ ∃ (t q:M),  t ∈ FUNC ∧ ‹ f,t› ∈ z ∧ ‹ x,q› ∈ t ∧ ‹  q,w› ∈ f:=
  assume z f,
  begin
    intros hf hz x w,
    split,
    {
      intro h,
      rw Ap_members at h,
      cases h with y h2,
      cases h2 with h3 h4,
      rw Church_successor at h3,
      dsimp at h3,
      rw comprehension at h3,
      cases h3 with h5 h6,
      cases h6 with g h7,
      cases h7 with p h8,
      cases h8 with h9 h10,
      rw ordered_pair_equality at h9,
      cases h9 with h12 h11,
      rw← h12 at *,
      rw← h11 at *,
      cases h10 with h13 h14,
      rw  h14  at h4,
      cases h4 with x1 h19,
      cases h19 with w1 h20,
      cases h20 with t h30,
      cases h30 with q h31,
      cases h31 with h32 h33,
      rw ordered_pair_equality at h32,
      cases h32 with h34 h35,
      rw← h34 at *,
      rw← h35 at *,
      use t, use q,
      exact h33,  
    },
    { 
      intro h,
      cases h with t h2,
      cases h2 with q h3,
      cases h3 with h4 h5,
      rcases h5 with ⟨ h6, h7, h8⟩, 
      rw Ap_members,
      rw Church_successor,
      dsimp,
      simp_rw comprehension,
      set Y:= setof(λ(v:M),  ∃ (t q x w:M), v =  ‹ x,w› ∧  t ∈ FUNC ∧ ‹ f,t › ∈ z ∧  ‹ x,q › ∈ t ∧ ‹ q,w› ∈ f) with h50,
      use Y,
      split,
      {
        split,
        {
          exact hz,
        },
        { 
          use f, use Y,
          simp,
          split,
          {
            exact hf,
          },
          { 
            intro u,
            split,
            { 
              intro h20,
              rw h50 at h20,
              rw comprehension at h20,
              cases h20 with t2 h31,
              cases h31 with q2 h32,
              cases h32 with x2 h33,
              cases h33 with w2 h34, 
              cases h34 with h21 h22,
              rw h21 at *, 
              cases h21 with h25 h26,
              use x2, use w2,
              simp,
              rcases h22 with ⟨ h23, h24, h25⟩, 
              use t2,
              split,
              {
                exact h23,
              },
              {
                split,
                { 
                  exact h24,
                },
                { 
                  use q2,
                  exact h25,
                }
              }
            },
            {  
              intro h40,
              rw h50,
              rw comprehension,
              cases h40 with x2 h50,
              cases h50 with w2 h51, 
              cases h51 with h52 h53,
              rw h52 at *,
              cases h53 with t2 h41,
              rcases h41 with ⟨ h42,h43,h44⟩, 
              rw FUNC_members at hz,
              have h45:= hz f t t2 h6 h43,
              rw← h45 at *,
              cases h44 with q2 h46,
              cases h46 with h47 h48,
              rw FUNC_members at hf,
              have h49:= hf q w w2 h8,
              use t2,
              use q2,
              use x2, 
              use w2,
              simp,
              rw h45 at *,
              exact ⟨ h4, h6, h47, h48⟩, 
            }
          }
        }
      },
      {
        rw h50,
        rw comprehension,
        use t, use q, use x, use w, 
        simp,
        exact ⟨ h4, h6, h7, h8⟩, 
      }
    }
  end
  
lemma sfunction2: ∀ (z:M), S z ∈ FUNC:=
  assume z,
  begin
    rw FUNC_members,
    intros x p q h3 h4,
    have h5:= Church_successor,
    rw h5 at *,
    dsimp at *,
    rw comprehension at *,
    cases h3 with h5 h6,
    cases h4 with h7 h8,
    cases h6 with f h9,
    cases h9 with p1 h10,
    cases h10 with h11 h12,
    rw ordered_pair_equality at h11,
    cases h11 with h13 h14,
    rw← h14 at *,
    rw h13 at *,
    cases h8 with g h15,
    cases h15 with q h16,
    cases h16 with h17 h18,
    rw ordered_pair_equality at h17,
    cases h17 with h19 h20,
    rw← h20 at *,
    rw← h19 at *, 
    cases h12 with h30 h31,
    cases h18 with h32 h33,
    rw full_extensionality,
    intro u,
    rw [h31,h33], 
  end
  
lemma srelation2: ∀ (z:M), Rel (S z):=
  assume z,
  begin
    rw Rel_definition,
    intros x h,
    have h5:= Church_successor,
    rw h5 at *,
    dsimp at *,
    rw comprehension at *, 
    cases h  with h5 h6,
    cases h6 with f h9,
    cases h9 with p  h10,
    cases h10 with h11 h12,
    rw h11 at *,
    use f, use p,
  end

lemma ChurchSuccessor3: ∀ (z f:M), f ∈ FUNC → z ∈ FUNC →  Rel (Ap (S z) f) :=
  assume z f,
  begin
    intros hf hz,
    rw Rel_definition,
    intros t h,
    rw Ap_members at h,
    cases h with y h2,
    cases h2 with h3 h4,
    rw Church_successor at h3,
    dsimp at h3,
    rw comprehension at h3,
    cases h3 with h5 h6,
    cases h6 with g h7,
    cases h7 with p h8,
    rcases h8 with ⟨ h9, h10, h11⟩, 
    rw ordered_pair_equality at h9,
    rw← h9.left at *,
    rw← h9.right at *,
    specialize h11 t,
    rw h11 at h4,
    cases h4 with x h12,
    cases h12 with w h13,
    cases h13 with s h14,
    cases h14 with r h15,
    cases h15 with h16 h17,
    use x, use w, 
    exact h16, 
  end
  
lemma ChurchSuccessor4: ∀ (f n:M), n ∈ FUNC → f ∈ FUNC → ∃ (y:M), ‹ f,y› ∈ S n ∧ Rel y:=
  assume f n hn hf,
  begin
    set y:= setof(λ (u:M), ∃ (x z p q:M), u = ‹ x,z› ∧ ‹ f,p› ∈ n 
            ∧ ‹ x,q › ∈ p ∧ ‹ q,z › ∈ f ∧ p ∈ FUNC) with h50,
    use y,
    split,
    {
      rw Church_successor,
      dsimp,
      rw comprehension,
      split,
      {
        exact hn,
      },
      {
        use f, use y,
        simp,
        split,
        {
          exact hf,
        },
        {
          intro u,
          split,
          {
            intro hu,
            rw h50 at hu,
            rw comprehension at hu,
            cases hu with x h51,
            cases h51 with w h52,
            cases h52 with p h53,
            cases h53 with q h54,
            rcases h54 with ⟨ h55, h56,h57,h58,h59⟩,
            use x, use w,
            split,
            {
              exact h55,
            },
            {
              use p,
              split, 
              {
                exact h59,
              },
              { 
                split,
                { 
                  exact h56,
                },
                {
                  use q,
                  exact ⟨ h57, h58⟩, 
                }
              },
            }
          },
          {
            intro h,
            cases h with x h2,
            cases h2 with z h3,
            cases h3 with h4 h5,
            cases h5 with p h6,
            rcases h6 with ⟨ h7, h8, h9⟩,
            cases h9 with q h10,
            cases h10 with h11 h12,
            rw h50,
            rw comprehension,
            use x, use z, use p, use q,
            exact ⟨ h4, h8, h11, h12, h7⟩, 
          }
        },
      }
    },
    {
      rw Rel_definition,
      intros z h60,
      rw h50 at h60,
      rw comprehension at h60,
      cases h60 with x h61,
      cases h61 with t h62,
      cases h62 with p h63,
      cases h63 with q h64,
      use x, use t,
      exact h64.left,
    }
  end

def Z_ChurchSuccessorMaps:= setof(λ (n:M), S n ∈ ℕℕ)

lemma Z_ChurchSuccessorMaps_members: ∀ (n:M), n ∈ Z_ChurchSuccessorMaps M ↔ S n ∈ ℕℕ:=
  assume n,
  begin
    unfold Z_ChurchSuccessorMaps,
    rw comprehension,
  end

def Z_nfFUNC:= setof(λ (n:M), n ∈ ℕℕ ∧ ∀ (f:M), f ∈ FUNC→ Rel f → ((Ap n f) ∈ FUNC ∧ Rel (Ap n f)  ))

lemma Z_nfFUNC_members: ∀ (n:M), n ∈ Z_nfFUNC M ↔  n ∈ ℕℕ ∧ ∀ (f:M), f ∈ FUNC → Rel f → ((Ap n f) ∈ FUNC ∧ Rel (Ap n f)):=
  assume n,
  begin
    unfold Z_nfFUNC,
    rw comprehension,
  end
  
def Z_iteration:= setof(λ(n:M), n ∈ ℕℕ ∧  ∀ (X f:M), f ∈ FUNC→ Rel f →maps M f X X→ (maps M (Ap n f) X X) ∧ ‹ f, Ap n f › ∈ n)

lemma Z_iteration_members: ∀ (n:M), n ∈ Z_iteration M ↔ n ∈ ℕℕ ∧ ∀ (X f:M), f ∈ FUNC→ Rel f  → maps M f X X→ (maps M (Ap n f) X X ∧ ‹ f, Ap n f › ∈ n):=
  assume n,
  begin
    unfold Z_iteration,
    rw comprehension, 
  end 

def Z_decidable0:= setof(λ(n:M), n ∈ ℕℕ ∧  (n = ChurchZero ∨ ¬ n = ChurchZero))

lemma Z_decidable0_members: ∀ (n:M), n ∈ Z_decidable0 M ↔ n ∈ ℕℕ ∧  (n = ChurchZero ∨ ¬ n = ChurchZero):=
  assume n,
  begin
    unfold Z_decidable0,
    rw comprehension, 
  end 

def Z_Rel:= setof(λ(x:M), Rel x)

lemma Z_Rel_members: ∀ (x:M), x ∈ Z_Rel M ↔ Rel x:=
  assume x,
  begin
    unfold Z_Rel,
    rw comprehension, 
  end

def Z_nf_defined:= setof(λ(n:M), n ∈ ℕℕ ∧  ∀ (f:M), f ∈ FUNC → ∃ (y:M), ‹ f,y› ∈ n ∧ Rel y)

lemma Z_nf_defined_members: ∀ (n:M), n ∈ Z_nf_defined M ↔ 
n ∈ ℕℕ ∧  ∀ (f:M), f ∈ FUNC → ∃ (y:M), ‹ f,y› ∈ n ∧ Rel y:=
  assume n, 
  begin
    unfold Z_nf_defined,
    rw comprehension, 
  end

def Z_predecessor:= setof(λ (x:M), x ∈ ℕℕ ∧ (¬ x = ChurchZero → ∃ (y:M), y ∈ ℕℕ  ∧ S y = x))

lemma Z_predecessor_members: ∀ (x:M), x ∈ Z_predecessor M ↔ x ∈ ℕℕ ∧ (¬ x = ChurchZero → ∃ (y:M), y ∈ ℕℕ  ∧ S y = x):=
  assume x,
  begin
    unfold Z_predecessor,
    rw comprehension, 
  end

def Z_zeroplusx := setof(λ (x:M), x ∈ ℕℕ ∧ ChurchZero ⊕ x = x)

lemma Z_zeroplusx_members: ∀ (x:M), x ∈ Z_zeroplusx M ↔ x ∈ ℕℕ ∧ ChurchZero ⊕ x = x :=
  assume x,
  begin
    unfold Z_zeroplusx,
    rw comprehension,
  end 

def Z_ChurchSuccessorShift:= setof(λ(n:M), n ∈ ℕℕ ∧  ∀(x:M), x ∈ ℕℕ → x ⊕ S n = (S x) ⊕ n)

lemma Z_ChurchSuccessorShift_members: ∀ (n:M), n ∈ Z_ChurchSuccessorShift M ↔ 
 n ∈ ℕℕ ∧  ∀(x:M), x ∈ ℕℕ → x ⊕ S n = (S x) ⊕ n :=
  assume n,
  begin
    unfold Z_ChurchSuccessorShift,
    rw comprehension,
  end 

def Z_ChurchAdditionMaps:= setof(λ (y:M), y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ → x ⊕ y ∈ ℕℕ)

lemma Z_ChurchAdditionMaps_members: ∀ (y:M), y ∈ Z_ChurchAdditionMaps M ↔ y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ → x ⊕ y ∈ ℕℕ:=
  assume y,
  begin
    unfold Z_ChurchAdditionMaps,
    rw comprehension, 
  end

def Z_ChurchAdditionAssociative:= setof(λ(y:M), y ∈ ℕℕ ∧  ∀ (x z:M), x ∈ ℕℕ → z ∈ ℕℕ → (x⊕y)⊕z = x ⊕ (y⊕z))

lemma Z_ChurchAdditionAssociative_members: ∀ (y:M), y ∈ Z_ChurchAdditionAssociative M ↔ y ∈ ℕℕ ∧  ∀ (x z:M), x ∈ ℕℕ → z ∈ ℕℕ → (x⊕y)⊕z = x ⊕ (y⊕z):=
  assume y,
  begin
    unfold Z_ChurchAdditionAssociative,
    rw comprehension,
  end 

def Z_ChurchAdditionCommutative:= setof(λ(y:M), y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ → x ⊕ y = y ⊕ x)

lemma Z_ChurchAdditionCommutative_members: ∀ (y:M), y ∈ Z_ChurchAdditionCommutative M ↔ y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ → x ⊕ y = y ⊕ x:=
  assume y,
  begin
    unfold Z_ChurchAdditionCommutative,
    rw comprehension,
  end

def Z_doubleiteration:= setof(λ(j:M), j ∈ ℕℕ ∧ ∀ (X f ℓ x:M),  f ∈ FUNC → maps M f X X → ℓ ∈ ℕℕ → x ∈ X → Ap (Ap j f)(Ap (Ap ℓ f) x) = Ap(  Ap (j ⊕ ℓ) f) x) 

lemma Z_doubleiteration_members: ∀ (j:M), j ∈  Z_doubleiteration M ↔
j ∈ ℕℕ ∧ ∀ (X f ℓ x:M), f ∈ FUNC → maps M f X X → ℓ ∈ ℕℕ → x ∈ X → Ap (Ap j f)(Ap (Ap ℓ f) x) = Ap(  Ap (j ⊕ ℓ) f) x:=
  assume j,
  begin
    unfold Z_doubleiteration,
    rw comprehension, 
  end 

def Z_iterationFUNC:= setof(λ (n:M), n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → dom (Ap n f) ⊆ X)

lemma Z_iterationFUNC_members: ∀ (n:M), n ∈ Z_iterationFUNC M ↔ n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → dom (Ap n f) ⊆ X:=
  assume n,
  begin
    unfold Z_iterationFUNC,
    rw comprehension,
  end

def Z_iterationRel:= setof(λ (n:M), n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → Rel (Ap n f) )

lemma Z_iterationRel_members: ∀ (n:M), n ∈ Z_iterationRel M ↔ n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → Rel (Ap n f) :=
  assume n,
  begin
    unfold Z_iterationRel,
    rw comprehension,
  end

def Z_iterationRange:= setof(λ (n:M), n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → range (Ap n f) ⊆ X)

lemma Z_iterationRange_members: ∀ (n:M), n ∈ Z_iterationRange M ↔ n ∈ ℕℕ ∧  ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → range (Ap n f) ⊆ X :=
  assume n,
  begin
    unfold Z_iterationRange,
    rw comprehension,
  end

def Z_zerosmall:= setof(λ (x:M), x ∈ ℕℕ ∧ (¬ x = ChurchZero → ChurchZero <ℕ x))

lemma Z_zerosmall_members: ∀ (x:M), x ∈ Z_zerosmall M ↔  x ∈ ℕℕ ∧ (¬ x = ChurchZero → ChurchZero <ℕ x):=
  begin
    intro x,
    unfold Z_zerosmall,
    rw comprehension,
  end

def Z_trichotomy1:= setof(λ(x:M),  x ∈ ℕℕ ∧ ∀(y:M), y ∈ ℕℕ → x <ℕ y ∨ x = y ∨ y <ℕ x)

lemma Z_trichotomy1_members: ∀ (x:M), x ∈ Z_trichotomy1 M ↔   x ∈ ℕℕ ∧  ∀(y:M), y ∈ ℕℕ → x <ℕ y ∨ x = y ∨ y <ℕ x :=
  assume x,
  begin
    unfold Z_trichotomy1,
    rw comprehension,
  end 

def Z_trichotomyonS(P:M):= setof(λ(y:M), y ∈ ℕℕ ∧  (y ∈ P →  ∀(x:M), x ∈ P → ¬ (x <ℕ y ∧ y <ℕ x) ∧ ¬ (y <ℕ y)))

lemma Z_trichotomyonS_members(P:M): ∀ (y:M), y ∈ Z_trichotomyonS M P ↔ y ∈ ℕℕ ∧ (y ∈ P →  ∀(x:M), x ∈ P → ¬ (x <ℕ y ∧ y <ℕ x) ∧ ¬ (y <ℕ y)):=
  assume y,
  begin
    unfold Z_trichotomyonS,
    rw comprehension,
  end 

def Z_Soneone:= setof(λ(p:M), p ∈ ℕℕ ∧  ∀ (u v:M), u ∈ ℕℕ → v ∈ ℕℕ → p = S u → S u = S v → u = v)

lemma Z_Soneone_members: ∀ (p:M), p ∈ Z_Soneone M ↔  p ∈ ℕℕ ∧  ∀ (u v:M), u ∈ ℕℕ → v ∈ ℕℕ → p = S u → S u = S v → u = v:=
  assume p,
  begin
    unfold Z_Soneone,
    rw comprehension, 
  end 

def Z_Spred:= setof(λ(x:M), x ∈ STEM  ∧ (x = ChurchZero  ∨  ∃(y:M), S y = x ∧ y ∈ STEM))

lemma Z_Spred_members: ∀ (x:M), x ∈ Z_Spred M ↔ x ∈ STEM  ∧ (x = ChurchZero  ∨  ∃(y:M), S y = x ∧ y ∈ STEM):=
  assume x,
  begin 
    unfold Z_Spred,
    rw comprehension,
  end

def Z_Sdecidable:= setof(λ(x:M),x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ → x ∈ STEM → (x = y ∨ ¬ x=y))

lemma Z_Sdecidable_members: ∀ (x:M), x ∈ Z_Sdecidable M ↔ x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ → x ∈ STEM → (x = y ∨ ¬ x=y):=
  assume x,
  begin
    unfold Z_Sdecidable,
    rw comprehension,
  end

def Z_Sinit:= setof(λ(y:M),  y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ →  y ∈ STEM → x <ℕ y → x ∈ STEM)

lemma Z_Sinit_members: ∀ (y:M), y ∈ Z_Sinit M ↔ y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ →  y ∈ STEM → x <ℕ y → x ∈ STEM:=
  assume y,
  begin
    unfold Z_Sinit,
    rw comprehension,
  end

def Z_Smax(k:M):= setof(λ (x:M), x ∈ STEM ∧ (x <ℕ k ∨ x = k))

lemma Z_Smax_members(k:M): ∀ (k:M), ∀(x:M), x ∈ Z_Smax M k ↔  x ∈ STEM ∧ (x <ℕ  k ∨ x = k):=
  begin
    unfold Z_Smax,
    intros k x,
    rw comprehension,
  end

def Z_knotlessthank(k:M):= setof(λ(x:M), x ∈ ℕℕ ∧  k <ℕ x)

lemma Z_knotlessthank_members(k:M): ∀ (k:M), ∀ (x:M), x ∈ Z_knotlessthank M k ↔ x ∈ ℕℕ ∧  k <ℕ x:=
  begin
    unfold Z_knotlessthank,
    intros k x,
    rw comprehension,
  end 

def Z_LcapS1 (k n:M):= setof(λ (j:M), j ∈ ℕℕ ∧ (j ∈ STEM → ¬ j ∈ LOOP n))

lemma Z_LcapS1_members(k n:M): ∀ (k n:M), ∀ (j:M), j ∈ Z_LcapS1 M k n ↔ j ∈ ℕℕ ∧ (j ∈ STEM → ¬ j ∈ LOOP n):=
  begin
    unfold Z_LcapS1,
    intros n k j,
    rw comprehension,
  end

def Z_LcupS (k n:M):= setof(λ (j:M), j ∈ ℕℕ ∧  j ∈ ((LOOP n) ∪ STEM))

lemma Z_LcupS_members(k n:M):  ∀ (j:M), j ∈ Z_LcupS M k n ↔ j ∈ ℕℕ ∧  j ∈ ((LOOP n) ∪ STEM):=
  begin
    unfold Z_LcupS,
    intros j,
    rw comprehension,
  end

def Tail (n:M):= setof(λ(x:M), n <ℕ x ∨ x = n)

lemma Tail_members (n:M):  ∀ (x:M), x ∈ Tail M n ↔ n <ℕ x ∨ x = n:=
  begin
    intro x,
    unfold Tail,
    rw comprehension,
  end

def Z_oneoneiteration:= setof(λ(m:M),m ∈ ℕℕ ∧  ∀ (X f:M), f∈ FUNC → Rel f → dom f ⊆ X → range f ⊆ X → maps M f X X → oneone M f X X →
maps M (Ap m f) X X ∧ oneone M (Ap m f) X X ∧ (¬ m = ChurchZero → range (Ap m f) ⊆ X ∧ dom (Ap m f) ⊆ X))

lemma Z_oneoneiteration_members: ∀ (m:M), m ∈ Z_oneoneiteration M ↔ m ∈ ℕℕ ∧  ∀ (X f:M), f∈ FUNC → Rel f → dom f ⊆ X → range f ⊆ X → maps M f X X → oneone M f X X →
maps M (Ap m f) X X ∧ oneone M (Ap m f) X X ∧ (¬ m = ChurchZero → range (Ap m f) ⊆ X ∧ dom (Ap m f) ⊆ X):=
  assume m,
  begin 
    unfold Z_oneoneiteration,
    rw comprehension, 
  end

def Z_klessthann(k n:M):= setof(λ (x:M), x ∈ STEM ∧ x ≤ℕ n)

lemma Z_klessthann_members(k n:M): ∀ (x:M), x ∈ Z_klessthann M k n ↔ x ∈ STEM ∧ x ≤ℕ n  :=
  assume m,
  begin
    unfold Z_klessthann,
    rw comprehension,
  end

def Z_looponto(k n:M):= setof(λ (x:M), x ∈ LOOP n ∧ ∃ (y:M), y ∈ LOOP n ∧ S y = x)

lemma Z_looponto_members(k n:M): ∀ (x:M), x ∈ Z_looponto M k n ↔ x ∈ LOOP n ∧ ∃ (y:M), y ∈ LOOP n ∧ S y = x:=
  assume x,
  begin
    unfold Z_looponto,
    rw comprehension,
  end

def W_dedekind1:= setof(λ (X:M),  X ∈ FINITE M  ∧  ∀ (f:M), oneone M f X X → Rel f → dom f = X→ onto M f X X )

lemma W_dedekind1_members: ∀ (X:M), X ∈ W_dedekind1 M ↔  X ∈ FINITE M  ∧ ∀ (f:M), oneone M f X X → Rel f → dom f = X → onto M f X X :=
  assume X,
  begin
    unfold W_dedekind1,
    rw comprehension,  
  end 

def W_dedekind2:= setof(λ (Y:M),  Y ∈ FINITE M ∧  ∀ (X:M), X ∈ FINITE M →
  Nc M X ≤ Nc M Y → 
  ∀ (f:M), f ∈ FUNC → Rel f → dom f ⊆ X → 
  (∀ (x:M), x ∈ X → ∃ (y:M), y ∈ Y ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∃ (x:M), x ∈ X ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∀  (x z:M), x ∈ X → z ∈ X → ‹ x,y› ∈ f → ‹ z,y› ∈ f → x=z))

lemma W_dedekind2_members: ∀ (Y:M), Y ∈ W_dedekind2 M ↔  Y ∈ FINITE M ∧  ∀ (X:M), X ∈ FINITE M →
  Nc M X ≤ Nc M Y → 
  ∀ (f:M), f ∈ FUNC → Rel f → dom f ⊆ X → 
  (∀ (x:M), x ∈ X → ∃ (y:M), y ∈ Y ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∃ (x:M), x ∈ X ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∀  (x z:M), x ∈ X → z ∈ X → ‹ x,y› ∈ f → ‹ z,y› ∈ f → x=z):=
  assume Y,
  begin
    unfold W_dedekind2,
    rw comprehension, 
  end 

-- preimage is for f:X → X  and seems wrong to me 7.9.25 as y is extra and unused
def preimage (f X y:M):= setof(λ(x:M), x ∈ X ∧ ∃ (y:M), y ∈ X ∧ ‹ x,y› ∈ f)

lemma preimage_members(f X y:M): ∀ (x:M), x ∈ preimage M f X y ↔ x ∈ X ∧ ∃ (y:M), y ∈ X ∧ ‹ x,y› ∈ f:=
  assume x,
  begin
    unfold preimage,
    rw comprehension,
  end 

-- preimage2 is for f:X → some set containing Y
def preimage2 (f X Y:M):= setof(λ(x:M), x ∈ X ∧ ∃ (y:M), y ∈ Y ∧ ‹ x,y› ∈ f)

lemma preimage2_members(f X Y:M): ∀ (x:M), x ∈ preimage2 M f X Y ↔ x ∈ X ∧ ∃ (y:M), y ∈ Y ∧ ‹ x,y› ∈ f:=
  assume x,
  begin
    unfold preimage2,
    rw comprehension,
  end 

lemma preimage2_subset(f X Y:M): preimage2 M f X Y ⊆ X:=
  begin
    unfold preimage2,
    rw subset_definition,
    intros z,
    rw comprehension,
    intros h,
    exact h.1,
  end

def CSG(n:M):= setof(λ (u:M), ∃ (x:M), u = ‹ x,S x› ∧ x ∈ LOOP n)

lemma CSG_members(n:M): ∀ (u:M), u ∈ CSG M n ↔ ∃ (x:M), u = ‹ x,S x› ∧ x ∈ LOOP n:=
  assume u,
  begin
    unfold CSG,
    rw comprehension, 
  end

def Z_precmin:= setof(λ (x:M),x ∈ ℕℕ ∧ ChurchZero ≼ x)

lemma Z_precmin_members: ∀ (x:M), x ∈ Z_precmin M ↔ x ∈ ℕℕ ∧  ChurchZero ≼ x:=
  assume x,
  begin
    unfold Z_precmin,
    rw comprehension,
  end

def Z_precmax(n:M):= setof(λ (x:M),x ∈ ℕℕ ∧ x ≼ n)

lemma Z_precmax_members(n:M): ∀ (x:M), x ∈ Z_precmax M n ↔ x ∈ ℕℕ ∧ x ≼ n:=
  assume x,
  begin
    unfold Z_precmax,
    rw comprehension,
  end

def Z_finiteinduction (X:M) := setof(λ(z:M), z∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ →  x ≼ z → x ∈ X)

lemma Z_finiteinduction_members(X:M) : ∀ (z:M), z ∈ Z_finiteinduction M X ↔ z∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ →  x ≼ z → x ∈ X:=
  assume z,
  begin
    unfold Z_finiteinduction,
    rw comprehension,
  end

def Z_prectrichotomy1:= setof(λ(x:M), x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ → x ≼ y ∨ y ≼ x)

lemma Z_prectrichotomy1_members: ∀ (x:M), x ∈ Z_prectrichotomy1 M ↔ x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ → x ≼ y ∨ y ≼ x:=
  assume x,
  begin
    unfold Z_prectrichotomy1,
    rw comprehension,
  end 

def Z_successorprec (n:M):= setof(λ (x:M), x ∈ ℕℕ ∧   ∀ (y:M), y ∈ ℕℕ → ¬ (y=n) → S y ≺ x → y ≼ x)

lemma Z_successorprec_members(n:M): ∀ (x:M), x ∈ Z_successorprec M n ↔ x ∈ ℕℕ ∧   ∀ (y:M), y ∈ ℕℕ → ¬ (y=n) → S y ≺ x → y ≼ x:=
  assume x,
  begin
    unfold Z_successorprec,
    rw comprehension,
  end

def Z_prectrichotomy2 := setof(λ(y:M), y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ  → ¬ (x=y) → ¬ (x ≼ y ∧ y ≼ x))

lemma Z_prectrichotomy2_members: ∀ (y:M), y ∈ Z_prectrichotomy2 M ↔ y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ  → ¬ (x=y) → ¬ (x ≼ y ∧ y ≼ x):=
  assume y,
  begin
    unfold Z_prectrichotomy2,
    rw comprehension,
  end 

def Z_sxnotprecx (x:M):= setof(λ(u:M), u ∈ ℕℕ ∧ ¬ (S x ≼ u  ∧  u ≼  x))

lemma Z_sxnotprecx_members(x:M): ∀ (u:M), u ∈ Z_sxnotprecx M x ↔ u ∈ ℕℕ ∧ ¬ (S x ≼ u  ∧  u ≼ x):=
  assume u,
  begin
    unfold Z_sxnotprecx,
    rw comprehension,
  end

def Z_finiteimpliesdoublesuccessor:= setof(λ(u:M), u ∈ ℕℕ  ∧ u ∈ STEM ∧ ∃ (v:M), v ∈ ℕℕ ∧ ¬ (u=v) ∧ S u = S v)

lemma Z_finiteimpliesdoublesuccessor_members: ∀(u:M), u ∈ Z_finiteimpliesdoublesuccessor M ↔ u ∈ ℕℕ  ∧ u ∈ STEM ∧ ∃ (v:M), v ∈ ℕℕ ∧ ¬ (u=v) ∧ S u = S v:=
  assume u,
  begin 
    unfold Z_finiteimpliesdoublesuccessor,
    rw comprehension,
  end 

def Z_ChurchMultiplicationMaps := setof(λ (y:M), y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ → x ⊗ y ∈ ℕℕ)

lemma Z_ChurchMultiplicationMaps_members: ∀ (y:M), y ∈ Z_ChurchMultiplicationMaps M ↔ y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ → x ⊗ y ∈ ℕℕ:=
  assume y,
  begin
    unfold Z_ChurchMultiplicationMaps,
    rw comprehension, 
  end

def Z_zerotimes:= setof(λ (y:M),y ∈ ℕℕ ∧  ChurchZero ⊗ y = ChurchZero)

lemma Z_zerotimes_members: ∀ (y:M), y ∈ Z_zerotimes M ↔ y ∈ ℕℕ ∧ ChurchZero ⊗ y = ChurchZero :=
  assume y,
  begin
    unfold Z_zerotimes,
    rw comprehension,
  end

def Z_successortimes:= setof(λ (y:M), y ∈ ℕℕ  ∧ ∀ (x:M), x ∈ ℕℕ  → S x ⊗ y = x ⊗ y ⊕ y)

lemma Z_successortimes_members: ∀ (y:M),y ∈ Z_successortimes M ↔ y ∈ ℕℕ  ∧ ∀ (x:M), x ∈ ℕℕ  → S x ⊗ y = x ⊗ y ⊕ y :=
  assume y,
  begin
    unfold Z_successortimes,
    rw comprehension,
  end

def Z_Church_leftdistrib:= setof(λ(x:M), x ∈ ℕℕ ∧  ∀ (y z:M),y ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊕ z) = x ⊗ y ⊕ x  ⊗ z)

lemma Z_Church_leftdistrib_members: ∀ (x:M), x ∈ Z_Church_leftdistrib M ↔ x ∈ ℕℕ ∧  ∀ (y z:M),y ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊕ z) = x ⊗ y ⊕ x  ⊗ z:=
  assume z,
  begin 
    unfold Z_Church_leftdistrib,
    rw comprehension,
  end 

def Z_Church_rightdistrib:= setof(λ(z:M), z ∈ ℕℕ ∧  ∀ (x y:M),x ∈ ℕℕ → y ∈ ℕℕ → (x ⊕ y) ⊗ z = x ⊗ z ⊕ y ⊗ z  )

lemma Z_Church_rightdistrib_members: ∀ (z:M), z ∈ Z_Church_rightdistrib M ↔ z ∈ ℕℕ ∧  ∀ (x y:M),x ∈ ℕℕ → y ∈ ℕℕ → (x ⊕ y) ⊗ z = x ⊗ z ⊕ y ⊗ z  :=
  assume z,
  begin 
    unfold Z_Church_rightdistrib,
    rw comprehension,
  end 

def Z_ChurchMultiplicationAssociative:= setof(λ (y:M), y ∈ ℕℕ ∧  ∀ (x z:M), x ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z )

lemma Z_ChurchMultiplicationAssociative_members: ∀ (y:M), y ∈ Z_ChurchMultiplicationAssociative M ↔ y ∈ ℕℕ ∧  ∀ (x z:M), x ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊗ z) = (x ⊗ y) ⊗ z :=
  assume y,
  begin 
    unfold Z_ChurchMultiplicationAssociative,
    rw comprehension, 
  end

def Z_ChurchMultiplicationCommutative:= setof (λ (y:M), y ∈ ℕℕ ∧ ∀ (x:M), x ∈ ℕℕ → x ⊗ y = y ⊗ x)

lemma Z_ChurchMultiplicationCommutative_members: ∀ (y:M), y ∈ Z_ChurchMultiplicationCommutative M ↔ y ∈ ℕℕ ∧  ∀ (x:M), x ∈ ℕℕ →  x ⊗ y = y ⊗ x :=
  assume y,
  begin
    unfold Z_ChurchMultiplicationCommutative,
    rw comprehension,
  end 

def W_leastelement(n:M):= setof(λ(X:M), X ∈ FINITE M ∧ ( X ⊆ ℕℕ → ¬ (X = Λ) → ∃ (p:M), p ∈ X ∧ ∀ (q:M),q ∈ X → p ≼ q ))

lemma W_leastelement_members(n:M): ∀ (X:M), X ∈ W_leastelement M n ↔  X ∈ FINITE M ∧ (X ⊆ ℕℕ → ¬ (X = Λ) → ∃ (p:M), p ∈ X ∧ ∀ (q:M),q ∈ X → p ≼ q):=
  assume X,
  begin
    unfold W_leastelement,
    rw comprehension,
  end 

def Zp(p:M):= setof(λ(x:M), x ∈ ℕℕ ∧ x ≺ p)

lemma Zp_members(p:M): ∀ (x:M), x ∈ Zp M p ↔ x ∈ ℕℕ ∧ x ≺ p:=
  assume x,
  begin
    unfold Zp,
    rw comprehension,
  end

 

def PRIME := setof(λ (p:M), p ∈ ℕℕ ∧ ¬ (p = ChurchZero) ∧ ¬ (p = S ChurchZero) ∧ ∀ (x:M), x ∈ ℕℕ → divides x p → x = S ChurchZero ∨ x = p)

lemma prime_members: ∀ (p:M), p ∈ PRIME M ↔  p ∈ ℕℕ ∧ ¬ (p = ChurchZero) ∧ ¬ (p = S ChurchZero) ∧ ∀ (x:M), x ∈ ℕℕ → divides x p → x = S ChurchZero ∨ x = p:=
  assume p,
  begin
    unfold PRIME,
    rw comprehension,
  end

 

def Z_precsum:= setof(λ(b:M), b ∈ ℕℕ ∧ ∀ (a:M), a ∈ ℕℕ → a ≼ b → ∃(x:M),x∈ ℕℕ ∧ a ⊕ x = b)

lemma Z_precsum_members: ∀ (b:M), b ∈ Z_precsum M ↔ b ∈ ℕℕ ∧ ∀ (a:M), a ∈ ℕℕ → a ≼ b → ∃(x:M),x∈ ℕℕ ∧ a ⊕ x = b:=
  assume b,
  begin
    unfold Z_precsum,
    rw comprehension,
  end
 
def order(x:M) := setof(λ(u:M), ∃ (j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x ∧ 
( ∀ (p:M), p ∈ ℕℕ → Ap (Ap p  (SG M)) ChurchZero = x → j ≼ p) ∧  u ∈ j )

lemma order_members(x:M): ∀ (u:M), u ∈ order M x ↔ ∃ (j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x ∧ 
( ∀ (p:M), p ∈ ℕℕ → Ap (Ap p  (SG M)) ChurchZero = x → j ≼ p) ∧  u ∈ j :=
  assume u,
  begin
    unfold order,
    rw comprehension, 
  end 

def Z_counting1:= setof(λ(x:M), x ∈ ℕℕ ∧ ∃ (j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero =x)

lemma Z_counting1_members: ∀ (x:M), x ∈ Z_counting1 M ↔ x ∈ ℕℕ ∧ ∃ (j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero =x :=
  assume x,
  begin
    unfold Z_counting1,
    rw comprehension,
  end 

def Z_counting2 (x:M):= setof(λ(j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x)

lemma Z_counting2_members(x:M): ∀ (j:M), j ∈ Z_counting2 M x ↔ j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x:=
  assume j,
  begin
    unfold Z_counting2,
    rw comprehension,
  end

def Z_kspreceq_helper(n:M):= setof(λ(l:M),l ∈ ℕℕ ∧  ∀ (j:M), j ∈ ℕℕ → j ≼ l → ¬ l = n → S j ≼ S l)

lemma Z_kspreceq_helper_members(n:M): ∀ (l:M), l ∈ Z_kspreceq_helper M n ↔
l ∈ ℕℕ ∧  ∀ (j:M), j ∈ ℕℕ → j ≼ l → ¬ l = n → S j ≼ S l:=
  assume l,
  begin
    unfold Z_kspreceq_helper,
    rw comprehension,
  end 

def Z_xsmapsloop(n:M):= setof(λ (x:M), x ∈ ℕℕ ∧  ∀ (y:M), y ∈ LOOP n → Ap (Ap x (SG M)) y ∈ LOOP n)

lemma Z_xsmapsloop_members(n:M): ∀ (x:M), x ∈ Z_xsmapsloop M n ↔ x ∈ ℕℕ ∧  ∀ (y:M), y ∈ LOOP n → Ap (Ap x (SG M)) y ∈ LOOP n:=
  assume x,
  begin
    unfold Z_xsmapsloop,
    rw comprehension,
  end

def Z_xsmapsN:= setof(λ (x:M), x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ  → Ap (Ap x (SG M)) y ∈ ℕℕ )

lemma Z_xsmapsN_members: ∀ (x:M), x ∈ Z_xsmapsN M ↔ x ∈ ℕℕ ∧  ∀ (y:M), y ∈ ℕℕ  → Ap (Ap x (SG M)) y ∈ ℕℕ :=
  assume x,
  begin
    unfold Z_xsmapsN,
    rw comprehension,
  end


def Z_ksprec(k:M):= setof(λ (l:M), l ∈ ℕℕ ∧ ∀ (j:M), j ∈ ℕℕ → j ≺ l → l ≼ k → 
Ap (Ap j (SG M)) ChurchZero ≺ Ap (Ap l (SG M)) ChurchZero ∧ 
Ap (Ap l (SG M)) ChurchZero ≼ Ap (Ap k (SG M)) ChurchZero)

lemma Z_ksprec_members(k:M): ∀ (l:M), l ∈ Z_ksprec M k ↔ 
l ∈ ℕℕ ∧ ∀ (j:M), j ∈ ℕℕ → j ≺ l → l ≼ k → 
Ap (Ap j (SG M)) ChurchZero ≺ Ap (Ap l (SG M)) ChurchZero ∧ 
Ap (Ap l (SG M)) ChurchZero ≼ Ap (Ap k (SG M)) ChurchZero:=
  assume l,
  begin
    unfold Z_ksprec,
    rw comprehension,
  end

def Z_mexists_helper(k n:M):= setof(λ(x:M), x ∈ ℕℕ ∧  ∃ (u:M), u ∈ ℕℕ ∧ x = n ⊕ u)

lemma Z_mexists_helper_members(k n:M):∀ (x:M), x ∈ Z_mexists_helper M k n ↔ x ∈ ℕℕ ∧  ∃ (u:M), u ∈ ℕℕ ∧ x = n ⊕ u:=
  assume x,
  begin
    unfold Z_mexists_helper,
    rw comprehension,
  end 

def Z_mexists(k n:M):= setof(λ (x:M), x ∈ ℕℕ ∧ n = k ⊕ x)

lemma Z_mexists_members(k n:M): ∀(x:M), x ∈ Z_mexists M k n ↔ x ∈ ℕℕ ∧ n = k ⊕ x:=
  assume x,
  begin
    unfold Z_mexists,
    rw comprehension,
  end

def Z_qsx(n:M):= setof(λ (q:M), q ∈ ℕℕ ∧  ∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x ∈ LOOP n)

lemma Z_qsx_members(n:M): ∀ (q:M), q ∈ Z_qsx M n ↔ q ∈ ℕℕ ∧  ∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x ∈ LOOP n:=
  assume q,
  begin
    unfold Z_qsx,
    rw comprehension,
  end

def Z_loopaddition(n:M):= setof(λ (z:M), z ∈ LOOP n ∧  ∃ (x:M), x ∈ ℕℕ ∧ z = n ⊕ x)

lemma Z_loopaddition_members(n:M): ∀ (z:M), z ∈ Z_loopaddition M n ↔ z ∈ LOOP n ∧  ∃ (x:M), x ∈ ℕℕ ∧ z = n ⊕ x:=
  assume z,
  begin
    unfold Z_loopaddition,
    rw comprehension,
  end 

def Z_orderq_helper(n q:M):= setof(λ(x:M), x ∈ LOOP n ∧ Ap (Ap q (SG M)) x = x)

lemma Z_orderq_helper_members(n q:M): ∀ (x:M), x ∈ Z_orderq_helper M n q ↔ x ∈ LOOP n ∧ Ap (Ap q (SG M)) x = x:=
  assume x,
  begin
    unfold Z_orderq_helper,
    rw comprehension,
  end 

def Z_orderq(n:M):= setof(λ (x:M), x ∈ ℕℕ ∧ ¬ x = ChurchZero ∧  Ap (Ap x (SG M)) n = n)
  
lemma Z_orderq_members(n:M): ∀ (x:M), x ∈ Z_orderq M n ↔ x ∈ ℕℕ ∧ ¬ x = ChurchZero ∧ Ap (Ap x (SG M)) n = n:=
  assume x,
  begin
    unfold Z_orderq,
    rw comprehension,
  end

def Z_additionmapsloop(n x:M):= setof(λ (y:M),  y ∈ ℕℕ  ∧  x ⊕ y ∈ LOOP n)

lemma Z_additionmapsloop_members(n x:M): ∀ (y:M), y ∈ Z_additionmapsloop M n x ↔ y ∈ ℕℕ  ∧  x ⊕ y ∈ LOOP n:=
  assume y,
  begin
    unfold Z_additionmapsloop,
    rw comprehension, 
  end

def Z_successoronloop(f x:M):= setof(λ(q:M), q ∈ ℕℕ ∧  Ap (Ap q f) x = Ap (Ap q (SG M)) x)

lemma Z_successoronloop_members(f x:M): ∀ (q:M), q ∈ Z_successoronloop M f x ↔ q ∈ ℕℕ ∧  Ap (Ap q f) x = Ap (Ap q (SG M)) x:=
  assume q,
  begin
    unfold Z_successoronloop,
    rw comprehension,
  end

def Z_E4424 (f α m n:M):= setof(λ (q:M), q ∈ ℕℕ ∧ (¬ q = n → S q ≺ m → Ap (Ap q f) α = Ap (Ap q (SG M)) α ))

lemma Z_E4424_members(f α m n:M): ∀ (q:M), q ∈ Z_E4424 M f α m n ↔ q ∈ ℕℕ ∧ (¬ q = n → S q ≺ m → Ap (Ap q f) α = Ap (Ap q (SG M)) α ):=
  assume q,
  begin
    unfold Z_E4424,
    rw comprehension,
  end

def Z_successorflip(q:M):= setof(λ(t:M), t ∈ ℕℕ ∧ 
Ap (Ap q (SG M)) (S t) = S (Ap (Ap q (SG M)) t))

lemma Z_successorflip_members(q:M): ∀ (t:M), t ∈ Z_successorflip M q ↔ t ∈ ℕℕ ∧ 
Ap (Ap q (SG M)) (S t) = S (Ap (Ap q (SG M)) t):=
  assume t,
  begin
    unfold Z_successorflip,
    rw comprehension,
  end 

def Z_E4672(n f:M):= setof(λ(q:M), q ∈ ℕℕ ∧  ∀(x:M), x ∈ LOOP n → Ap (Ap q f) x = Ap (Ap q (SG M)) x)

lemma Z_E4672_members(n f:M): ∀ (q:M), q ∈ Z_E4672 M n f ↔ q ∈ ℕℕ ∧  ∀(x:M), x ∈ LOOP n → Ap (Ap q f) x = Ap (Ap q (SG M)) x:=
  assume q,
  begin
    unfold Z_E4672,
    rw comprehension,
  end

def Z_xfmaps( f X x:M):= setof(λ (q:M), q ∈ ℕℕ  ∧  Ap (Ap q f) x ∈ X)

lemma Z_xfmaps_members(f X x:M): ∀ (q:M), q ∈ Z_xfmaps M f X x ↔ q ∈ ℕℕ  ∧  Ap (Ap q f) x ∈ X:=
  assume q,
  begin
    unfold Z_xfmaps,
    rw comprehension, 
  end

def Z_orderq_helper2(n q:M):= setof(λ (t:M), t ∈ LOOP n ∧  ( Ap (Ap q (SG M)) t = t →  ∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M) ) x = x))

lemma Z_orderq_helper2_members(n q:M): ∀ (t:M), t ∈ Z_orderq_helper2 M n q ↔ t ∈ LOOP n ∧  ( Ap (Ap q (SG M)) t = t →  ∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M) ) x = x):=
  assume t,
  begin
    unfold Z_orderq_helper2,
    rw comprehension,
  end 

def Z_stemseparable_helper:= setof(λ (u:M), ∃ (x y:M), u = ‹ x,y › ∧ S x = S y ∧ x ∈ ℕℕ ∧ y ∈ ℕℕ ∧ ¬ y = x)

lemma Z_stemseparable_helper_members: ∀ (u:M), u ∈ Z_stemseparable_helper M ↔ ∃ (x y:M), u = ‹ x,y › ∧ S x = S y ∧ x ∈ ℕℕ ∧ y ∈ ℕℕ ∧ ¬ y = x :=
  assume u,
  begin 
    unfold Z_stemseparable_helper,
    rw comprehension,
  end 

def Z_stemseparable:= setof (λ(x:M), x ∈ ℕℕ ∧  (x ∈ STEM ∨ ¬ x ∈ STEM))

lemma Z_stemseparable_members: ∀ (x:M), x ∈ Z_stemseparable M ↔ x ∈ ℕℕ ∧  (x ∈ STEM ∨ ¬ x ∈ STEM):=
  assume x,
  begin
    unfold Z_stemseparable,
    rw comprehension,
  end

def R_kinstem_helper:= setof(λ (u:M), ∃ (x y:M), u = ‹ y,x › ∧ S x = S y ∧ x ∈ ℕℕ ∧ y ∈ ℕℕ ∧ ¬ y = x ∧ x ∈ STEM )

lemma R_kinstem_helper_members: ∀ (u:M), u ∈ R_kinstem_helper M ↔ ∃ (x y:M), u = ‹ y,x › ∧ S x = S y ∧ x ∈ ℕℕ ∧ y ∈ ℕℕ ∧ ¬ y = x ∧ x ∈ STEM :=
  assume u,
  begin 
    unfold R_kinstem_helper,
    rw comprehension,
  end 

def Z_kinstem_helper:= setof(λ (x:M), x ∈ ℕℕ ∧ ∃ (y:M),  y ∈ ℕℕ ∧ ‹ y,x› ∈ R_kinstem_helper M)

lemma Z_kinstem_helper_members: ∀ (x:M), x ∈ Z_kinstem_helper M ↔ x ∈ ℕℕ ∧ ∃ (y:M),  y ∈ ℕℕ ∧ ‹ y,x› ∈ R_kinstem_helper M:=
  assume x,
  begin
    unfold Z_kinstem_helper,
    rw comprehension,
  end

def JLift:= setof(λ(u:M),∃(p q:M), u = ‹ single p, q ›  ∧ ∀ (w:M), 
  (‹ single ChurchZero, single ChurchZero › ∈ w 
    ∧ ∀ (x y:M), ‹ single x, y › ∈ w → ¬ S x ∈ y → 
    ‹ single(S x), y ∪ single (S x) › ∈ w ) → u ∈ w)

lemma JLift_members: ∀ (u:M), u ∈ JLift M ↔ ∃(p q:M), u = ‹ single p, q ›  ∧ ∀ (w:M), 
  (‹ single ChurchZero, single ChurchZero › ∈ w 
    ∧ ∀ (x y:M),‹ single x, y › ∈ w → ¬ S x ∈ y → 
    ‹ single (S x), y ∪ single (S x) › ∈ w ) → u ∈ w:=
  assume u,
  begin
    unfold JLift,
    rw comprehension,
  end

def Z_JLiftfinite := setof(λ (u:M),∃(p q:M), u = ‹ single p, q › ∧ u ∈ JLift M ∧ q ∈ FINITE M ∧ q ⊆ ℕℕ ∧ p ∈ ℕℕ )

lemma Z_JLiftfinite_members: ∀ (u:M), u ∈ Z_JLiftfinite M ↔ ∃(p q:M), u = ‹ single p, q › ∧ u ∈ JLift M ∧ q ∈ FINITE M ∧ q ⊆ ℕℕ ∧ p ∈ ℕℕ :=
  assume u,
  begin
    unfold Z_JLiftfinite,
    rw comprehension,
  end

def Z_union2(x:M):= setof(λ(y:M), y ∈ FINITE M ∧ ¬¬ (x ∪ y ∈ FINITE M))

lemma Z_union2_members(x:M): ∀ (y:M), y ∈ Z_union2 M x ↔ y ∈ FINITE M ∧ ¬¬ (x ∪ y ∈ FINITE M):=
  assume y,
  begin
    unfold Z_union2,
    rw comprehension,
  end 

def Z_JLiftMaps_helper:= setof(λ(p:M), p ∈ JLift M ∧  ∃(x y:M), p = ‹ single x, y › ∧ ChurchZero ∈ y ∧ x ∈ y ∧ ∀(u:M), u ∈ y → ¬ u = x → S u ∈ y) 

lemma Z_JLiftMaps_helper_members: ∀ (p:M), p ∈ Z_JLiftMaps_helper M ↔  p ∈ JLift M ∧  ∃(x y:M), p = ‹ single x, y › ∧ ChurchZero ∈ y ∧ x ∈ y ∧ ∀(u:M), u ∈ y → ¬ u = x → S u ∈ y:=
  assume p,
  begin
    unfold Z_JLiftMaps_helper,
    rw comprehension,
  end 

def Z_JLiftMaps:= setof(λ(x:M),x ∈ ℕℕ ∧  ∃(y:M), ‹ single x, y › ∈ JLift M)

lemma Z_JLiftMaps_members: ∀ (x:M), x ∈ Z_JLiftMaps M ↔ x ∈ ℕℕ ∧ ∃(y:M), ‹ single x, y › ∈ JLift M:=
  assume x,
  begin
    unfold Z_JLiftMaps,
    rw comprehension,
  end

def JC(x:M):= setof(λ(z:M), ∀ (y:M), ‹ single x, y › ∈ JLift M → z ∈ y)

lemma JC_members(x:M): ∀ (z:M), z∈ JC M (x) ↔  ∀ (y:M), ‹ single x, y › ∈ JLift M → z ∈ y :=
  assume u,
  begin
    unfold JC,
    rewrite comprehension, 
  end

def Z_JRec:= setof(λ(x:M),  x ∈ ℕℕ ∧  JC M (S x) = ((JC M x) ∪ single (S x)))

lemma Z_JRec_members: ∀ (x:M), x ∈ Z_JRec M ↔  x ∈ ℕℕ ∧  JC M (S x) = ((JC M x) ∪ single (S x)):=
  assume x,
  begin
    unfold Z_JRec,
    rw comprehension,
  end

def W_JLift2:= setof (λ (z:M), z ∈ JLift  M ∧ ( z = ‹ single ChurchZero, single ChurchZero› ∨ 
        ( ∃ (x y:M), z = ‹ single (S x), y› ∧  x ∈ ℕℕ) ∧ 
        (  ∀  (x y:M),  z = ‹ single (S x), y› →  x ∈ ℕℕ →  ∃ (u p:M), ‹ single u, p › ∈ JLift M ∧ x ∈ ℕℕ  ∧ u ∈ ℕℕ ∧  S u = S x ∧    ¬ S u ∈ p ∧ y = (p ∪ single (S u)))))

lemma W_JLift2_members: ∀ (z:M), z ∈ W_JLift2  M ↔ z ∈ JLift  M ∧  (z = ‹ single ChurchZero, single ChurchZero› ∨ 
             ( ∃ (x y:M), z = ‹ single (S x), y› ∧  x ∈ ℕℕ) ∧ 
             (  ∀  (x y:M),  z = ‹ single (S x), y› → x ∈ ℕℕ →   ∃ (u p:M), ‹ single u, p › ∈ JLift M ∧ x ∈ ℕℕ  ∧ u ∈ ℕℕ ∧  S u = S x ∧   ¬ S u ∈ p ∧ y = (p ∪ single (S u)))):=
  assume z,
  begin
    unfold W_JLift2,
    rw comprehension, 
  end 

def W_JLiftdom:= setof (λ (z:M), z ∈ JLift M ∧ (z = ‹ single ChurchZero, single ChurchZero› ∨ ∃ (u y: M), z = ‹ single (S u), y › ∧ u ∈ ℕℕ ))

lemma W_JLiftdom_members: ∀ (z:M), z ∈ W_JLiftdom M ↔ z ∈ JLift M ∧ (z = ‹ single ChurchZero, single ChurchZero› ∨ ∃ (u y: M), z = ‹ single (S u), y › ∧ u ∈ ℕℕ ):=
  assume z,
  begin
    unfold W_JLiftdom,
    rw comprehension,
  end

def comparable(x y:M):= ¬¬ ( x ⊆ y ∨ y ⊆ x)

def W_JLiftcomparable:= setof(λ(u:M), u ∈ JLift M ∧ ∀ (x p:M), u = ‹ single x, p› → 
∀ (y q:M), ‹ single y,q› ∈ JLift M → comparable M p q)

lemma W_JLiftcomparable_members: ∀ (u:M), u ∈ W_JLiftcomparable M ↔
u ∈ JLift M ∧ ∀(x p:M), u = ‹ single x, p› →  
∀ (y q:M), ‹ single y,q› ∈ JLift M → comparable M p q:=
  assume u,
  begin
    unfold W_JLiftcomparable,
    rw comprehension,
  end

def Z_functionality:= setof(λ(x:M), x ∈ ℕℕ ∧ (∀ (y z:M),‹ single x,y › ∈ JLift M → ‹ single x,z› ∈ JLift M → y = z))

lemma Z_functionality_members: ∀ (x:M), x ∈ Z_functionality M ↔ x ∈ ℕℕ ∧ (∀ (y z:M),‹ single x,y › ∈ JLift M → ‹ single x,z› ∈ JLift M → y = z):=
  assume x,
  begin
    unfold Z_functionality,
    rw comprehension,
  end

def Z_domaindecidability:= setof (λ(x:M), x ∈ ℕℕ ∧ (∀ (y p t:M),‹ single x,y› ∈ JLift M → ‹ single t,p› ∈ JLift M → x = t ∨ ¬ x=t))

lemma Z_domaindecidability_members: ∀ (x:M), x ∈ Z_domaindecidability M ↔ x ∈ ℕℕ ∧ (∀ (y p t:M),‹ single x,y› ∈ JLift M → ‹ single t,p› ∈ JLift M → x = t ∨ ¬ x=t):=
  assume x,
  begin
    unfold Z_domaindecidability,
    rw comprehension,
  end 
 
def Z_comparability:= setof(λ(x:M), x ∈ ℕℕ ∧ (∀ (y p t:M),‹ single x,y› ∈ JLift M → ‹ single t,p› ∈ JLift M → comparable M y p ))

lemma Z_comparability_members: ∀ (x:M), x ∈ Z_comparability M ↔ x ∈ ℕℕ ∧ (∀ (y p t:M),‹ single x,y› ∈ JLift M → ‹ single t,p› ∈ JLift M → comparable M y p ):=
  assume x,
  begin
    unfold Z_comparability,
    rw comprehension,
  end 
 
def Z_decidableequality:= setof(λ(x:M), x ∈ ℕℕ ∧ ∀(y:M), y ∈ ℕℕ → x = y ∨ ¬ x = y)

lemma Z_decidableequality_members: ∀ (x:M), x ∈ Z_decidableequality M ↔ x ∈ ℕℕ ∧ ∀(y:M), y ∈ ℕℕ → x = y ∨ ¬ x = y:=
  assume x,
  begin
    unfold Z_decidableequality,
    rw comprehension,
  end

def Z_Jcardinality:= setof(λ (m:M), m ∈ 𝔽 ∧ 𝕁 M m ∈ 𝕋 M (𝕋 M m))

lemma Z_Jcardinality_members: ∀ (m:M), m ∈ Z_Jcardinality M ↔ m ∈ 𝔽 ∧ 𝕁 M m ∈ 𝕋 M (𝕋 M m):=
  assume m,
  begin
    unfold Z_Jcardinality,
    rw comprehension,
  end 

def ChurchFrege:= setof(λ (u:M), (∃(p q:M), u = ‹ p,q› ∧ p ∈ ℕℕ ∧ q ∈ 𝔽 ) ∧  ∀ (w:M), ‹ ChurchZero, zero› ∈ w → (∀ (p q:M), ‹p,q› ∈ w → 𝕊 q ∈ 𝔽 → ‹ S p, 𝕊 q › ∈ w) → u ∈ w)

lemma ChurchFrege_members: ∀ (u:M), u ∈ ChurchFrege M ↔ (∃(p q:M), u = ‹ p,q› ∧ p ∈ ℕℕ ∧ q ∈ 𝔽 ) ∧ ∀ (w:M), ‹ ChurchZero, zero› ∈ w → (∀ (p q:M), ‹p,q› ∈ w → 𝕊 q ∈ 𝔽 → ‹ S p, 𝕊 q › ∈ w) → u ∈ w:=
  assume u,
  begin
    unfold ChurchFrege,
    rw comprehension,
  end 

def W_ChurchFrege:= setof(λ (u:M), ∃ (p q:M), u = ‹ p,q› ∧ ((p = ChurchZero ∧ q = zero) ∨ ∃ (t r:M), ‹ t,r› ∈ ChurchFrege M ∧ p = S t ∧ q = 𝕊 r))

lemma W_ChurchFrege_members: ∀ (u:M), u ∈ W_ChurchFrege M ↔ ∃ (p q:M), u = ‹ p,q› ∧ ((p = ChurchZero ∧ q = zero) ∨ ∃ (t r:M), ‹ t,r› ∈ ChurchFrege M ∧ p = S t ∧ q = 𝕊 r):=
  assume u,
  begin
    unfold W_ChurchFrege,
    rw comprehension,
  end

def Z_ChurchFrege2:= setof(λ (p:M), p ∈ ℕℕ ∧  ∀(q r:M), ‹ p,q› ∈  ChurchFrege M → ‹ p,r › ∈  ChurchFrege M → q=r)

lemma Z_ChurchFrege2_members: ∀ (p:M),p ∈ Z_ChurchFrege2 M ↔ p ∈ ℕℕ ∧   ∀(q r:M), ‹ p,q› ∈  ChurchFrege M → ‹ p,r › ∈  ChurchFrege M → q=r:=
  assume p,
  begin
    unfold Z_ChurchFrege2,
    rw comprehension,
  end 

def Z_ChurchRosserhelper:= setof(λ(x:M), x ∈ ℕℕ ∧ ∀ (y z:M), ‹ x,y › ∈ ChurchFrege M → ‹ Ap (Ap x (SG M)) ChurchZero, z›  ∈ ChurchFrege M → 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M z))))) = y)

lemma Z_ChurchRosserhelper_members: ∀ (x:M), x ∈ Z_ChurchRosserhelper M ↔ x ∈ ℕℕ ∧ ∀ (y z:M), ‹ x,y › ∈ ChurchFrege M → ‹ Ap (Ap x (SG M)) ChurchZero, z›  ∈ ChurchFrege M → 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M z))))) = y:=
  assume x,
  begin
    unfold Z_ChurchRosserhelper,
    rw comprehension,
  end 

def Z_ChurchFregeonto:= setof(λ(y:M),y ∈ 𝔽 ∧ ∃ (x:M), x ∈ ℕℕ ∧ ‹ x,y› ∈ ChurchFrege M)

lemma Z_ChurchFregeonto_members: ∀ (y:M), y ∈ Z_ChurchFregeonto M ↔ y ∈ 𝔽 ∧ ∃ (x:M), x ∈ ℕℕ ∧ ‹ x,y› ∈ ChurchFrege M:=
  assume y,
  begin
    unfold Z_ChurchFregeonto,
    rw comprehension,
  end

def Z_ChurchFregeoneone:= setof(λ(y:M),  y ∈ 𝔽 ∧  ∀ (x z:M), ‹ x,y › ∈ ChurchFrege M → ‹ z,y › ∈ ChurchFrege M → x = z)

lemma Z_ChurchFregeoneone_members: ∀(y:M), y ∈ Z_ChurchFregeoneone M ↔  y ∈ 𝔽 ∧  ∀ (x z:M), ‹ x,y › ∈ ChurchFrege M → ‹ z,y › ∈ ChurchFrege M → x = z:=
  assume y,
  begin
    unfold Z_ChurchFregeoneone,
    rw comprehension,
  end 

def Z_successorinhabited:= setof(λ(x:M), x ∈ 𝔽 ∧ ∃ (u:M), u ∈ 𝕊 x)

lemma Z_successorinhabited_members: ∀ (x:M), x ∈ Z_successorinhabited M ↔ x ∈ 𝔽 ∧ ∃ (u:M), u ∈ 𝕊 x:=
  assume x,
  begin
    unfold Z_successorinhabited,
    rw comprehension,
  end

def Z_jFUNC:= setof(λ (x:M), x ∈ 𝔽 ∧  ∀ (y z:M), ‹ y,x › ∈ ChurchFrege M → ‹ z,x› ∈ ChurchFrege M → y = z)

lemma Z_jFUNC_members: ∀ (x:M), x ∈ Z_jFUNC M ↔  x ∈ 𝔽 ∧  ∀ (y z:M), ‹ y,x › ∈ ChurchFrege M → ‹ z,x› ∈ ChurchFrege M → y = z :=
  assume x,
  begin
    unfold Z_jFUNC,
    rw comprehension,
  end 

def Z_jhelper:= setof(λ (x:M), x ∈ 𝔽 ∧  ∀ (y z:M), ‹ y,x› ∈ ChurchFrege M → ‹ z, 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))))›  ∈ ChurchFrege M →   Ap( Ap y (SG M)) ChurchZero = z )

lemma Z_jhelper_members: ∀ (x:M), x ∈ Z_jhelper M ↔ x ∈ 𝔽 ∧  ∀ (y z:M), ‹ y,x› ∈ ChurchFrege M → ‹ z, 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) › ∈ ChurchFrege M →   Ap( Ap y (SG M)) ChurchZero = z :=
  assume x,
  begin
    unfold Z_jhelper,
    rw comprehension,
  end

def Z_orderstep(t g f a b:M):= setof(λ(r:M),r ∈ ℕℕ ∧ (r ≺ t → Ap (Ap r g) a = Ap (Ap r f) a ∧ ¬ Ap (Ap r f) a = b))

lemma Z_orderstep_members(t g f a b:M): ∀ (r:M), r ∈ Z_orderstep M t g f a b ↔ r ∈ ℕℕ ∧ (r ≺ t → Ap (Ap r g) a = Ap (Ap r f) a ∧ ¬ Ap (Ap r f) a = b) :=
  assume r,
  begin
    unfold Z_orderstep,
    rw comprehension,
  end
  
def injection(f X:M):Prop := oneone M f X X ∧ Rel f ∧ f ∈ FUNC ∧ dom f ⊆ X ∧ range f ⊆ X
def permutation(f X:M):Prop := injection M f X ∧ onto M f X X
def cyclicperm (f X a:M) := permutation M f X ∧  a ∈ X ∧ ∀ (z:M), z ∈ X → ∃ (r:M), r ∈ ℕℕ ∧ z = Ap (Ap r f) a
def permorder (f X a q:M) := q ∈ ℕℕ ∧ Ap (Ap q f) a = a ∧ (∀ (t:M), t ∈ ℕℕ → t ≼ q → ¬ t = ChurchZero → Ap (Ap t f) a = a → t = q) ∧ ∀(x:M),x ∈ X → ∃ (r:M), r ∈ ℕℕ ∧ r ≼ q ∧ Ap( Ap r f) a = x

def Z_allorders:= setof(λ (q:M), q ∈ ℕℕ ∧ (¬ q = ChurchZero → ¬ q = S ChurchZero → ¬¬ ∃ (X f a:M), X ∈ FINITE M ∧ cyclicperm M f X a ∧ permorder M f X a q))

lemma Z_allorders_members: ∀ (q:M), q ∈ Z_allorders M ↔ q ∈ ℕℕ ∧ ( ¬ q = ChurchZero → ¬ q = S ChurchZero → ¬¬ ∃ (X f a:M), X ∈ FINITE M ∧ cyclicperm M f X a ∧ permorder M f X a q):=
  assume q,
  begin
    unfold Z_allorders,
    rw comprehension,
  end

def W_finiteperm:= setof(λ(X:M),  X ∈ FINITE M ∧ (X = Λ ∨ ∃ (a f q:M), a ∈ X  ∧  cyclicperm M f X a ∧ permorder M f X a q))

lemma W_finiteperm_members: ∀ (X:M), X ∈ W_finiteperm M ↔  X ∈ FINITE M ∧ (X = Λ ∨ ∃ (a f q:M), a ∈ X  ∧  cyclicperm M f X a ∧ permorder M f X a q):=
  assume X,
  begin
    unfold W_finiteperm,
    rw comprehension, 
  end 

def Z_3051(a f:M) := setof(λ(t:M), t ∈ ℕℕ ∧ Ap (Ap t f) a = a)

lemma Z_3051_members(a f:M) : ∀ (t:M), t ∈ Z_3051 M a f ↔ t ∈ ℕℕ ∧ Ap (Ap t f) a = a:=
  assume t,
  begin
    unfold Z_3051,
    rw comprehension,
  end

def Z_gf (a f g n:M):= setof(λ(r:M), r ∈ ℕℕ ∧ ( ¬ r = n → ¬ r = ChurchZero → Ap (Ap r g) a = Ap (Ap (S r) f) a))

lemma Z_gf_members(a f g n:M): ∀ (r:M), r ∈ Z_gf M a f g n ↔ r ∈ ℕℕ ∧ (¬ r = n → ¬ r = ChurchZero → Ap (Ap r g) a = Ap (Ap (S r) f) a):=
  assume r,
  begin
    unfold Z_gf,
    rw comprehension,
  end

def X_nomaxU (f a x:M):= setof(λ (r:M),r ∈ ℕℕ ∧ x = Ap(Ap r f) a)

lemma X_nomaxU_members(f a x:M): ∀ (r:M), r ∈ X_nomaxU M f a x ↔ r ∈ ℕℕ ∧ x = Ap(Ap r f) a:=
  assume r,
  begin
    unfold X_nomaxU,
    rw comprehension,
  end

def Z_tripleexphelper:= setof(λ(p:M),p ∈ 𝔽 ∧ ∀ (q:M),q ∈  𝔽 → exp M (𝕋 M p) = 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ q = exp M r)

lemma Z_tripleexphelper_members: ∀ (p:M), p ∈ Z_tripleexphelper M ↔ p ∈ 𝔽 ∧  ∀ (q:M),q ∈  𝔽 →  exp M (𝕋 M p) = 𝕋 M q → ∃ (r:M), r ∈ 𝔽 ∧ q = exp M r:=
  assume p,
  begin
    unfold Z_tripleexphelper,
    rw comprehension,
  end 

def Z_Tsum2:= setof (λ(r:M), r ∈ 𝔽 ∧    ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → 𝕋 M n + 𝕋 M m = 𝕋 M r →  n+m = r)

lemma Z_Tsum2_members: ∀ (r:M), r ∈ Z_Tsum2 M ↔ r ∈ 𝔽 ∧    ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → 𝕋 M n + 𝕋 M m = 𝕋 M r →  n+m = r:=
  assume r,
  begin
    unfold Z_Tsum2,
    rw comprehension,
  end
  
--def Z_expT2:= setof(λ (k:M), k ∈ 𝔽 ∧  ∀ (r:M), r ∈ 𝔽  → exp M (𝕋 M k) = 𝕋 M r → r = exp M k)


def R_Tkappa3 (a f U:M):= setof(λ (x:M), x ∈ a ∧  x ∈  U ∧ ∀ (y:M), ‹ single x, y › ∈ f → ¬ x ∈ y)

lemma R_Tkappa3_members(a f U:M): ∀(x:M),x ∈ R_Tkappa3 M a f U ↔ x ∈ a ∧ x ∈  U ∧ ∀ (y:M), ‹ single x, y › ∈ f → ¬ x ∈ y:=
  assume x,
  begin
    unfold R_Tkappa3,
    rw comprehension,
  end

def W_finite_structure:= setof(λ (z:M), z ∈ FINITE M ∧ (z = Λ ∨ ∃ (x c:M), x ∈ FINITE M ∧ ¬ c ∈ x ∧ z = (x ∪ (single c))))

lemma W_finite_structure_members: ∀ (z:M), z ∈ W_finite_structure M ↔ z ∈ FINITE M ∧ (z = Λ ∨ ∃ (x c:M), x ∈ FINITE M ∧ ¬ c ∈ x ∧ z = (x ∪ (single c))):=
  assume z,
  begin
    unfold W_finite_structure,
    rw comprehension, 
  end

def Z_Finfinite:= setof(λ (m:M), m ∈ 𝔽 ∧   ∃ (u:M), u ∈ 𝕊 m)

lemma Z_Finfinite_members: ∀(m:M), m ∈ Z_Finfinite M ↔ m ∈ 𝔽  ∧ ∃ (u:M), u ∈ 𝕊 m:= 
  assume m,
  begin
    unfold Z_Finfinite,
    rw comprehension, 
  end

def Z_maximal(m:M):= setof (λ (x:M), x ∈ 𝔽 ∧  x ≤ m)

lemma Z_maximal_members(m:M): ∀(x:M), x ∈ Z_maximal M m ↔ (x ∈ 𝔽 ∧  x ≤ m):=
  assume x,
  begin
    unfold Z_maximal, 
    rw comprehension,
  end 

def Z_lambdatimesx := setof (λ(x:M), x ∈ SF M ∧ (¬ x = zero → Λ * x = Λ)  )

lemma Z_lambdatimesx_members: ∀ (x:M), x ∈ Z_lambdatimesx M ↔ x ∈ SF M ∧ (¬ x = zero → Λ * x = Λ):=
  assume x,
  begin
    unfold Z_lambdatimesx,
    rw comprehension,
  end

def Z_xtimeslambda_helper:= setof (λ(u:M), ∃ (x r:M), u = triple x Λ r ∧ x ∈ 𝔽 ∧ one < x ∧ ¬ (r = Λ)  )

lemma Z_xtimeslambda_helper_members: ∀ (u:M), u ∈ Z_xtimeslambda_helper M ↔ ∃ (x r:M), u = triple x Λ r ∧ x ∈ 𝔽 ∧ one < x ∧ ¬ (r = Λ) :=
  assume u,
  begin
    unfold Z_xtimeslambda_helper,
    rw comprehension,
  end

def Z_onetimeslambda := setof (λ(z:M), z ∈ 𝔽 ∧ triple one Λ z ∈ multiplication_graph M)

lemma Z_onetimeslambda_members: ∀ (z:M), z ∈ Z_onetimeslambda M ↔ z ∈ 𝔽 ∧ triple one Λ z ∈ multiplication_graph M:=
  assume z,
  begin
    unfold Z_onetimeslambda,
    rw comprehension,
  end

def Z_notnotleastmember (X:M):= setof (λ(m:M), m ∈ 𝔽 ∧ ∀(x:M), x ∈ 𝔽 → x < m → ¬ x ∈ X)

lemma Z_notnotleastmember_members (X:M): ∀ (m:M),  m ∈ Z_notnotleastmember M X ↔ m ∈  𝔽 ∧ ∀(x:M), x ∈ 𝔽 → x < m → ¬ x ∈ X:=
  assume m,
  begin 
    unfold Z_notnotleastmember,
    rw comprehension,
  end

def Z_mtimesx (m:M):= setof(λ(x:M), x ∈ SF M ∧ (x = zero ∨ x = one ∨ m*x = Λ)) 
lemma Z_mtimesx_members (m:M): ∀(x:M), x ∈ Z_mtimesx M m↔  x ∈ SF M ∧ (x = zero ∨x = one ∨ m*x = Λ):=
  assume x,
  begin
   unfold Z_mtimesx,
   rw comprehension,
  end

def Z_expquad2:= setof(λ(x:M), x ∈ SF M ∧ (¬ x*x = Λ → two < x → x+x+one < x*x))

lemma Z_expquad2_members: ∀ (x:M), x ∈ Z_expquad2 M ↔ x ∈ SF M ∧ ( ¬ x*x = Λ  → two < x → x + x + one < x*x):=
  assume x,
  begin
    unfold Z_expquad2,
    rw comprehension,
  end

def Z_maximalmulrec:= setof(λ (y:M), y ∈ SF M ∧  ∀(x:M),x ∈ SF M → x * (𝕊 y) = x * y + x  )

lemma Z_maximalmulrec_members: ∀ (y:M), y ∈ Z_maximalmulrec M ↔ y ∈ SF M ∧ ∀ (x:M), x ∈ SF M → x * (𝕊 y) = x*y + x:=
  assume y,
  begin
    unfold Z_maximalmulrec,
    rw comprehension,
  end 

def Z_multclosed:= setof(λ(u:M), u ∈ multiplication_graph M ∧  ∃ (x y z:M), u = triple x y z ∧ x ∈ SF M ∧ y ∈ SF M ∧ z ∈ SF M)

lemma Z_multclosed_members: ∀ (u:M), u ∈ Z_multclosed M ↔ 
(u ∈ multiplication_graph M ∧  ∃ (x y z:M), u = triple x y z ∧ x ∈ SF M ∧ y ∈ SF M ∧ z ∈ SF M):=
  assume u,
  begin
    unfold Z_multclosed,
    rw comprehension,
  end 

def Z_le_square:= setof(λ(y:M), y ∈ 𝔽 ∧  ∀(x:M), x ∈ 𝔽  → y* y ∈ 𝔽 → x ≤ y → x * x ∈ 𝔽 ∧ x * x ≤ y * y)

lemma Z_le_square_members: ∀ (y:M), y ∈ Z_le_square M ↔ y ∈ 𝔽 ∧  ∀(x:M), x ∈ 𝔽  → y* y ∈ 𝔽 → x ≤ y → x * x ∈ 𝔽 ∧ x * x ≤ y * y:=
  assume y,
  begin
    unfold Z_le_square,
    rw comprehension,
  end 

def half (x k:M) :=  (k ∈ SF M ∧ x = k+k) ∨ (k ∈ SF M ∧ x = k + k + one)
def even (x:M):=  exists (k:M), k ∈ SF M ∧ x = k+ k
def odd (x:M):=  exists (k:M), k ∈ SF M ∧ x = k +k+ one

def Z_div2:= setof(λ (x:M), x ∈ SF M ∧  ∃ (k:M), k ∈ SF M ∧ half M x k)

lemma Z_div2_members: ∀ (x:M), x ∈ Z_div2 M ↔ x ∈ SF M ∧  ∃ (k:M), k ∈ SF M ∧ half M x k:=
  assume x,
  begin
    unfold Z_div2,
    rw comprehension,
  end 


def Z_evenorodd:= setof(λ (x:M), x ∈ 𝔽 ∧ ((even M x ∧ ¬ odd M x) ∨ (odd M x ∧ ¬ even M x)) )

lemma Z_evenorodd_members: ∀(x:M), x ∈ Z_evenorodd M ↔ x ∈ 𝔽 ∧ ((even M x ∧ ¬ odd M x) ∨ (odd M x ∧ ¬ even M x)) :=
  assume x,
  begin 
    unfold Z_evenorodd,
    rw comprehension,
  end

def Z_halfunique:= setof(λ (x:M), x ∈ 𝔽 ∧  ∀(p q:M),  half M x p → half M x q  → p = q)

lemma Z_halfunique_members: ∀ (x:M), x ∈ Z_halfunique M ↔ x ∈ 𝔽 ∧  ∀(p q:M), half M x p → half M x q  → p = q :=
  assume x,
  begin  
    unfold Z_halfunique,
    rw comprehension,
  end

def Z_nonzeroissuccessorSF:= setof(λ(x:M), x ∈ SF M ∧ ( ¬(x =zero) → ∃(y:M), y ∈ SF M ∧  𝕊 y = x))

lemma Z_nonzeroissuccessorSF_members: ∀ (x:M), x ∈ Z_nonzeroissuccessorSF M ↔  x ∈ SF M ∧  ( ¬(x =zero) → ∃(y:M), y ∈ SF M ∧ 𝕊 y = x):=
  assume x,
  begin
    unfold Z_nonzeroissuccessorSF,
    rw comprehension,
  end 

def Z_multle:= setof(λ (y:M), y ∈ 𝔽 ∧  ∀ (x a b:M), x∈ 𝔽 → y ∈ 𝔽 → a ∈ 𝔽→ b ∈ 𝔽→ a < b → x < y → b * y ∈ 𝔽 → a *x < b * y)
lemma Z_multle_members: ∀ (y:M), y ∈ Z_multle M ↔ y ∈ 𝔽 ∧  ∀ (x a b:M), x∈ 𝔽 → y ∈ 𝔽 → a ∈ 𝔽→ b ∈ 𝔽→ a < b → x < y → b * y ∈ 𝔽 → a *x < b * y:=
  assume y,
  begin  
    unfold Z_multle,
    rw comprehension,
  end 

def Z_nozerodivisors:= setof(λ(y:M),  y ∈ 𝔽 ∧  ∀(x:M), x ∈ 𝔽  → x* y = zero → x = zero ∨ y = zero)

lemma Z_nozerodivisors_members: ∀ (y:M), y ∈ Z_nozerodivisors M ↔  y ∈ 𝔽 ∧  ∀(x:M), x ∈ 𝔽  →  x* y = zero → x = zero ∨ y = zero:=
  assume y,
  begin
    unfold Z_nozerodivisors,
    rw comprehension,
  end 

def Z_notnotfiniteunion:= setof (λ(x:M), x ∈ FINITE M ∧ ((∀ (y:M), y ∈ x → y ∈ FINITE M) →  ¬¬ union x ∈ FINITE M))

lemma Z_notnotfiniteunion_members: ∀ (x:M), x ∈ Z_notnotfiniteunion M ↔ x ∈ FINITE M ∧ ((∀ (y:M), y ∈ x → y ∈ FINITE M) → ¬¬ union x ∈ FINITE M) :=
  assume x,
  begin
    unfold Z_notnotfiniteunion,
    rw comprehension,
  end

def Z_addition_reverse (m:M):= setof(λ(q:M),q ∈ 𝔽 ∧  ∀ (p a:M), p ∈ 𝔽 →  a ∈ p → p+q < m → ¬¬ ∃ (b:M), b ∈q ∧ a ∩ b = Λ)

lemma Z_addition_reverse_members (m:M): ∀(q:M), q ∈ Z_addition_reverse M m ↔ q ∈ 𝔽 ∧  ∀ (p a:M), p ∈ 𝔽 →  a ∈ p → p+q < m → ¬¬ ∃ (b:M), b ∈q ∧ a ∩ b = Λ :=
  assume y,
  begin 
    unfold Z_addition_reverse,
    rw comprehension,
  end

def COFINITE (k:M):= k ∈ 𝔽 ∧ ∃ (u:M), 𝕍 - u ∈ k ∧ u ∈ FINITE M

def Z_cofinite:= setof(λ (k:M), COFINITE M k)
lemma Z_cofinite_members: ∀ (k:M), k ∈ Z_cofinite M ↔ COFINITE M k:=
  assume k,
  begin
    unfold Z_cofinite,
    rw comprehension,
  end

def Z_notnotssc2(x:M):= setof(λ(q:M), q ∈ x ∨ ¬ q ∈ x)
lemma Z_notnotssc2_members: ∀ (x q:M), q ∈ Z_notnotssc2 M x ↔ q ∈ x ∨ ¬ q ∈ x:=
  assume x q,
  begin
    unfold Z_notnotssc2,
    rw comprehension,
  end

def D_SSC2U(U f c:M):= setof(λ(x:M),x ∈ c ∧ x ∈ SSC U ∧ ¬ ∃(y:M), ‹single x, y›  ∈ f ∧  x ∈ y)
lemma D_SSC2U_members: ∀ (U f c x:M), x ∈ D_SSC2U M U f c ↔ x ∈ c ∧ x ∈ SSC U ∧ ¬ ∃(y:M), ‹single x, y› ∈ f ∧ x ∈y  :=
  assume U f c x,
  begin
    unfold D_SSC2U,
    rw comprehension,
  end

def Z_expT2(m:M):= setof(λ(u:M), u ∈ 𝔽 ∧  ((¬ u = 𝕋 M m) →  ∀(k:M), k ∈ 𝔽 → 𝕋 M k = exp M (𝕋 M u) → k = exp M u ))

lemma Z_expT2_members: ∀ (m u:M), u ∈ Z_expT2 M m ↔ u ∈ 𝔽 ∧ ((¬ u = 𝕋 M m) →  ∀ (k:M), k ∈ 𝔽  →  𝕋 M k = exp M (𝕋 M u)  → k = exp M u):=
  assume m u,
  begin
    unfold Z_expT2,
    rw comprehension,
  end

def Z_Vfinite:= setof (λ (x:M), ∀ (y:M), y ∈ 𝕍 → x ∈ (y ∪ (𝕍 -y)))
lemma Z_Vfinite_members:∀(x:M), x ∈ Z_Vfinite M ↔ ∀ (y:M), y ∈ 𝕍 → x ∈ (y ∪ (𝕍 -y)):=
  assume x,
  begin
    unfold Z_Vfinite,
    rw comprehension,
  end

def Z_Vfinite2(x:M) := setof(λ(y:M), x ∈ (y ∪ (𝕍 -y)))
lemma Z_Vfinite2_members: ∀ (x y:M), y ∈ Z_Vfinite2 M x ↔x ∈ (y ∪ (𝕍 -y)):=
  assume x y,
  begin
    unfold Z_Vfinite2,
    rw comprehension,
  end

def FSFS:= setof(λ(x:M), x ∈ FINITE M ∧ x ⊆ FINITE M )
lemma FSFS_members: ∀ (x:M), x ∈ FSFS M ↔ x ∈ FINITE M ∧ x ⊆ FINITE M :=
  assume x,
  begin
    unfold FSFS,
    rw comprehension,
  end 

def SMALL := setof(λ(n:M), n ∈ 𝔽 ∧ ∃ (x:M), x ∈ n ∧ x ∈ FSFS M)

lemma small_members: ∀ (n:M), n ∈ SMALL M ↔ n ∈ 𝔽 ∧ ∃ (x:M), x ∈ n ∧ x ∈ FSFS M:=
  assume n,
  begin
    unfold SMALL,
    rw comprehension,  
  end

def W_functionfinite:= setof(λ(A:M), A ∈ FINITE M ∧  ∀(B f:M),  B ∈ FINITE M →
  maps M f A B → ( ∀(x y:M), ‹x,y›   ∈ f → x ∈ A) → f ∈ FINITE M)
lemma W_functionfinite_members: ∀ (A:M),  A ∈ W_functionfinite M ↔ A ∈ FINITE M ∧  ∀(B f:M), B ∈ FINITE M →
  maps M f A B → ( ∀(x y:M), ‹x,y›   ∈ f → x ∈ A) → f ∈ FINITE M:=
  begin
    unfold W_functionfinite,
    intros A,
    rw comprehension,
  end

def W_finiteunion3(X:M):= setof(λ(y:M), y ∈ FINITE M ∧ (y ⊆ SSC X → union y ∈ FINITE M))
lemma W_finiteunion3_members: ∀ (X y:M), y ∈ W_finiteunion3 M X ↔ y ∈ FINITE M ∧ (y ⊆ SSC X → union y ∈ FINITE M):=
  begin
    intros X y,
    unfold W_finiteunion3,
    rw comprehension,
  end


def upsim(f c:M):= setof(λ(z:M), ∃(t y:M),z = ‹t,union  y › ∧ ‹ single t, y › ∈ f  ∧ t ∈ c )
lemma upsim_members: ∀(f c z:M),z ∈ upsim M f c ↔ ∃(t y:M),z = ‹t,union y › ∧ ‹ single t, y › ∈ f ∧ t ∈ c :=
  begin
    unfold upsim,
    intros f c z,
    rw comprehension,
  end 

def W_productfinite_helper2(a Y:M):= setof(λ(z:M),∃(y:M),z = ‹ single (single y), ‹ a, y› › ∧ y ∈ Y )
lemma W_productfinite_helper2_members: ∀(a Y z:M), z ∈ W_productfinite_helper2 M a Y ↔  ∃(y:M),z = ‹ single (single y), ‹ a, y› › ∧ y ∈ Y :=
  begin
    unfold W_productfinite_helper2,
    intros a f z,
    rw comprehension,
  end

def W_productfinite2:= setof(λ(X:M), X ∈ FINITE M ∧ ∀ (Y:M), Y ∈ FINITE M → X × Y ∈ FINITE M)
lemma W_productfinite2_members: ∀(X:M), X ∈ W_productfinite2 M ↔ X ∈ FINITE M ∧ ∀ (Y:M), Y ∈ FINITE M → X × Y ∈ FINITE M:=
  begin
    unfold W_productfinite2,
    intros X,
    rw comprehension,
  end

def W_dedekind3:= setof(λ(X:M), X ∈ FINITE M ∧ ∀(Y f:M), Y ∈ FINITE M → maps M f X Y → onto M f X Y → dom f = X → Nc M Y ≤ Nc M X)
lemma W_dedekind3_members: ∀ (X:M),X ∈ W_dedekind3 M ↔ X ∈ FINITE M ∧ ∀(Y f:M), Y ∈ FINITE M → maps M f X Y →  onto M f X Y → dom f = X → Nc M Y ≤ Nc M X:=
  begin 
    unfold W_dedekind3,
    intros X,
    rw comprehension,
  end 

def Diagonal (f c:M):= setof(λ(t:M), t∈ c  ∧ ∃(y:M), ‹single t,y› ∈ f ∧ ¬ t ∈ y)
lemma Diagonal_members(f c:M): ∀ (f c t:M), t ∈ Diagonal M f c ↔ t∈ c  ∧ ∃(y:M), ‹single t,y› ∈ f ∧ ¬ t ∈ y:=
  begin
    intros f c t,
    unfold Diagonal,
    rw comprehension,
  end

def Z_subsetoffinite(m:M) := setof(λ(k:M), k ∈ 𝔽 ∧ (k ≤ exp M (𝕋 M m) →  ¬¬ ∃(u:M), u ∈ k ∧ u ⊆ FINITE M))
lemma Z_subsetoffinite_members(m:M):∀ (k:M),k ∈ Z_subsetoffinite M m ↔ k ∈ 𝔽 ∧ (k ≤ exp M (𝕋 M m) → ¬¬ ∃(u:M), u ∈ k ∧ u ⊆ FINITE M):=
  begin 
    intros k,
    unfold Z_subsetoffinite,
    rw comprehension,
  end

def Z_sevenpointtwo(max:M):= setof(λ(p:M), p ∈ 𝔽 ∧  ∀ (m:M), m ∈ 𝔽 →  p = Nc M (Φ M m) →
 𝕋 M p  < Nc M (Φ M (𝕋 M m)) ) 
lemma Z_sevenpointtwo_members(max:M): ∀ (max p:M), p ∈ Z_sevenpointtwo M max ↔  
p ∈ 𝔽 ∧ ∀ (m:M), m ∈ 𝔽 →  p = Nc M (Φ M m) →
 𝕋 M p  < Nc M (Φ M (𝕋 M m)) :=
  begin
    intros max m,
    unfold Z_sevenpointtwo,
    rw comprehension, 
  end

def Z_sixpointtwo(m:M):= setof(λ (p:M), p ∈ 𝔽 ∧ (𝕊 p ∈ 𝔽 →  𝕀 M m (𝕊 p) = (Λ:M)))
lemma Z_sixpointtwo_members(m:M): ∀ (m p:M), p ∈ Z_sixpointtwo M m ↔  p ∈ 𝔽 ∧ (𝕊 p ∈ 𝔽 →  𝕀 M m (𝕊 p) = (Λ:M)):=
  begin
    intros p m,
    unfold Z_sixpointtwo,
    rw comprehension,
  end 

def Z_Irange(max m:M):= setof(λ (n:M), n ∈ 𝔽 ∧ (𝕀 M m n = (Λ:M) ∨ 𝕀 M m n ∈ 𝔽 ))
lemma Z_Irange_members(max m:M): ∀ (max m n:M), n ∈ Z_Irange M max m ↔  n ∈ 𝔽 ∧ (𝕀 M m n = (Λ:M) ∨ 𝕀 M m n ∈ 𝔽 ):=
  begin
    intros max m n,
    unfold Z_Irange,
    rw comprehension,
  end

def gphi(m:M):= setof(λ(p:M), ∃ (a b:M), p = ‹a,b› ∧ a ∈ 𝔽 ∧  𝕀 M m a = b)
lemma gphi_members(m:M): ∀ (p:M), p ∈ gphi M m↔  ∃ (a b:M), p = ‹a,b› ∧ a ∈ 𝔽 ∧  𝕀 M m a = b:=
  begin
   intros p,
   unfold gphi,
   rw comprehension,
  end

def Z_mplusonelessthanexpm:= setof(λ(p:M), p ∈ 𝔽 ∧ (¬ p = zero → ¬ p = one → exp M p ∈ 𝔽 → 𝕊 p < exp M p))
lemma Z_mplusonelessthanexpm_members: ∀ (p:M), p ∈ Z_mplusonelessthanexpm M ↔ p ∈ 𝔽 ∧ (¬ p = zero → ¬ p = one → exp M p ∈ 𝔽 → 𝕊 p < exp M p):=
  begin
    intros p,
    unfold Z_mplusonelessthanexpm,
    rw comprehension,
  end 

def doublecomplement(X:M):= setof(λ(x:M), ¬¬ x ∈ X)
lemma doublecomplement_members(X:M): ∀(x:M),x ∈ doublecomplement M X ↔ ¬¬ x ∈X:=
  begin 
    intros x,
    unfold doublecomplement,
    rw comprehension,
  end 

def HH := setof(λ(x:M),∀ (w:M),(zero ∈ w ∧  (∀ (z:M),z ∈ w → 𝕊 z ∈ w)) → x ∈ w ) 

-- I already used ℍ for something else so I just use HH here,
-- but in the paper I use ℍ 
lemma HH_members: ∀ (x:M), x ∈ HH M ↔ ∀ (w:M),((zero:M) ∈ w ∧  (∀ (z:M),z ∈ w → 𝕊 z ∈ w)) → x ∈ w :=
  begin
    intros x,
    unfold HH,
    rw comprehension, 
  end

def Z_nonzeroissuccessorH:= setof (λ(x:M), x ∈ HH M ∧ (¬ x = zero → ∃(y:M), y ∈ HH M ∧ 𝕊 y = x))
lemma Z_nonzeroissuccessorH_members: ∀ (x:M), x ∈ Z_nonzeroissuccessorH M ↔  x ∈ HH M ∧ (¬ x = zero → ∃(y:M), y ∈ HH M ∧ 𝕊 y = x):=
  begin
    intros x,
    unfold Z_nonzeroissuccessorH,
    rw comprehension,
  end

def Z_decidableHzero:= setof (λ (x:M), x ∈ HH M ∧ (x = zero ∨ ¬ x = zero)) 
lemma Z_decidableHzero_members: ∀(x:M), x ∈ Z_decidableHzero M ↔ x ∈ HH M ∧ (x = zero ∨ ¬ x = zero):=
  begin
    intros x,
    unfold Z_decidableHzero,
    rw comprehension,
  end

def Z_decidableequalityonH:= setof(λ (y:M),y ∈ HH M ∧  ∀ (x:M), x ∈ HH M → x = y ∨ ¬ x = y)
lemma Z_decidableequalityonH_members: ∀ (y:M),y ∈ Z_decidableequalityonH M ↔ y ∈ HH M ∧  ∀ (x:M),x ∈ HH M → x = y ∨ ¬ x = y:=
  begin
    intros y,
    unfold Z_decidableequalityonH,
    rw comprehension,
  end 

def Z_HtonotnotF:= setof(λ(x:M), x ∈ HH M ∧ ¬¬ x ∈ 𝔽)
lemma Z_HtonotnotF_members: ∀ (x:M), x ∈ Z_HtonotnotF M ↔ x ∈ HH M ∧ ¬¬ x ∈ 𝔽:=
  begin 
    intros x,
    unfold Z_HtonotnotF,
    rw comprehension,
  end

def successorHH:= setof(λ(z:M), ∃(x:M), x ∈ HH M ∧ z = ‹ x, 𝕊 x›  )
lemma successorHH_members: ∀ (z:M),(z ∈ successorHH M ↔ ∃(x:M), x ∈ HH M ∧ z = ‹ x, 𝕊 x›  ):=
  begin
    intros z,
    unfold successorHH,
    rw comprehension,
  end

def Z_monotonicity(m:M):= setof(λ(p:M),p ∈ 𝔽 ∧ ∀ (a b:M), a ∈ 𝔽 → b ∈ 𝔽 →   Nc M (Φ M a) = p→ a ≤ b → Nc M (Φ M b) ≤  p)
lemma Z_monotonicity_members(m:M): ∀ (p:M), p ∈ Z_monotonicity M m ↔ p ∈ 𝔽 ∧ ∀ (a b:M), a ∈ 𝔽 → b ∈ 𝔽 →   Nc M (Φ M a) = p→ a ≤ b → Nc M (Φ M b) ≤  p:=
  begin
    intros p,
    unfold Z_monotonicity,
    rw comprehension,
  end

def fnomax:=setof(λ(z:M), ∃ (x y:M), z = ‹x,y› ∧ 𝕀 M one x = y ∧ x∈ 𝔽  ∧ ∃(u:M),u∈ y )
lemma fnomax_members: ∀ (z:M), z ∈ fnomax M ↔ ∃ (x y:M), z = ‹x,y› ∧ 𝕀 M one x = y ∧ x∈ 𝔽  ∧ ∃(u:M),u∈ y :=
  begin
    intros z,
    unfold fnomax,
    rw comprehension,
  end

def membershipF (x y:M):= setof(λ(z:M), z ∈ y ∧ z = x)
lemma membershipF_members(x y:M): ∀ (z: M), z ∈ membershipF M x y ↔ z ∈ y ∧ z = x:=
  begin
    intros z,
    unfold membershipF,
    rw comprehension,
  end

def Z_towerNC (m:M):= setof(λ y, y ∈ 𝔽  ∧  ((∃ u, u ∈ 𝕀 M m y) → 𝕀 M m y ∈ NC M ))
lemma Z_towerNC_members : ∀(m y:M), y ∈ Z_towerNC M m ↔ y ∈ 𝔽 ∧ ( (∃ u, u ∈ 𝕀 M m y) → 𝕀 M m y ∈ NC M) :=
  assume m y,
  begin
    unfold Z_towerNC,
    rw comprehension, 
  end
  
def Z87(m:M):M := setof(λ y, y ∈ 𝔽 ∧  ( m ∈ NC M →  (∃ u, u ∈ 𝕀 M m y) → y ≤ 𝕀 M m y))
lemma Z87_members : ∀(m y:M), y ∈ Z87 M m ↔ y ∈ 𝔽 ∧ ( m ∈ NC M →  (∃ u, u ∈ 𝕀 M m y) → y ≤ 𝕀 M m y) :=
  assume m y,
  begin
    unfold Z87,
    rw comprehension, 
  end

def Z87F(m:M):M := setof(λ y, y ∈ 𝔽 ∧  ( m ∈ 𝔽  →  (∃ u, u ∈ 𝕀 M m y) → y ≤ 𝕀 M m y))
lemma Z87F_members : ∀(m y:M), y ∈ Z87F M m ↔ y ∈ 𝔽 ∧ ( m ∈ 𝔽  →  (∃ u, u ∈ 𝕀 M m y) → y ≤ 𝕀 M m y) :=
  assume m y,
  begin
    unfold Z87F,
    rw comprehension, 
  end

def imageT (X:M):=setof(λ(y:M),∃(u:M),u ∈ X ∧ y = 𝕋 M u)
lemma imageT_members(X:M): ∀ (X y:M), y ∈ imageT M X ↔ ∃(u:M),u ∈ X ∧ y = 𝕋 M u:=
  begin
    intros X y,
    unfold imageT,
    rw comprehension, 
  end

def W_Timage:= setof(λ(X:M), X ∈ FINITE M ∧ (X ⊆ NC M →  Nc M (imageT M X) = 𝕋 M (Nc M X)))
lemma W_Timage_members: ∀(X:M), X ∈ W_Timage M ↔    X ∈ FINITE M  ∧ (X ⊆ NC M →  Nc M (imageT M X) = 𝕋 M (Nc M X)):=
  begin
    intros X,
    unfold W_Timage,
    rw comprehension,
  end 

def USC_inverse(e:M):= setof(λ(x:M), single x ∈ e)
lemma USC_inverse_members(e:M): ∀ (x:M), x ∈ USC_inverse M e ↔ single x ∈ e:=
  begin
    intros x,
    unfold USC_inverse,
    rw comprehension,
  end

def Z_mlessthanImy(m:M):= setof(λ(y:M),y∈ 𝔽 ∧ ((¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → y < 𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽))
lemma Z_mlessthanImy_members(m:M): ∀(y:M), y ∈Z_mlessthanImy M m ↔ y∈ 𝔽 ∧ ( (¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → y < 𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽) :=  
  begin
    intros y,
    unfold Z_mlessthanImy,
    rw comprehension,
  end

def Z_towerbreakI(n x:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ((∃(u:M),u ∈ 𝕀 M (𝕀 M n x) y)→ x + y ∈ 𝔽 ∧ (𝕀 M n (x+y)) = 𝕀 M (𝕀 M n x) y))
lemma Z_towerbreakI_members(n x:M): ∀(y:M), y ∈ Z_towerbreakI M n x ↔ y ∈ 𝔽 ∧ ((∃(u:M),u ∈ 𝕀 M (𝕀 M n x) y)→ x + y ∈ 𝔽 ∧ (𝕀 M n (x+y)) = 𝕀 M (𝕀 M n x) y):=
  begin
    intros y,
    unfold Z_towerbreakI,
    rw comprehension,
  end



#axioms_all  -- This file is clean. 

