import inf25
-- theory of towergraphE
-- inf.lean grew too long so I am putting some
-- definitions by comprehension in this file too.  

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

def Z_towergraphE:M := setof(λ y,  y ∈ 𝔽 ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ towergraphE M)
def Z_towergraphE2:M := setof(λ y, y ∈ 𝔽  ∧ ∀ (x z w:M), (triple x y z ∈ towergraphE M ∧ triple x y w ∈ towergraphE M → z = w))
def Z_towerE_defined:M := setof(λ y, y ∈ 𝔽 ∧ ∀(m:M), ∃(z:M), triple m y z ∈ towergraphE M)
def Z_towerE_singlevalued:M := setof(λ y, y ∈ 𝔽  ∧ ∀ (m z w:M), triple m y z ∈ towergraphE M → triple m y w ∈ towergraphE M → z = w )
def W81E:M := setof(λ u, ∃(m y z:M), u = triple m y z ∧ triple m y z ∈ towergraphE M ∧ ( (y=zero ∧ z = m)  ∨ ∃ (p v w:M), y = 𝕊 p ∧ v ∈ y ∧ triple m p w ∈ towergraphE M ∧ z = exp2 M w))
def Z82E:M := setof(λ y, y ∈ 𝔽 ∧ ∀ (m z w:M), triple m y z ∈ towergraphE M → triple m y w ∈ towergraphE M → z = w)

lemma Z82E_members: ∀ (y:M), y ∈ Z82E M ↔ y ∈ 𝔽 ∧ ∀ (m z w:M), triple m y z ∈ towergraphE M → triple m y w ∈ towergraphE M → z = w:=
  assume y,
  begin
    unfold Z82E,
    rw comprehension,
  end 


lemma W81E_members: ∀ (u:M), u ∈ W81E M ↔ 
∃(m y z:M), u = triple m y z ∧ triple m y z ∈ towergraphE M ∧
( (y=zero ∧ z = m)  ∨ ∃ (u v w:M), y = 𝕊 u ∧ v ∈ y ∧ triple m u w ∈ towergraphE M ∧ z = exp2 M w):=
  assume u,
    begin
      unfold W81E,
      rw comprehension, 
    end

 
lemma Z_towergraphE_members: ∀(y:M), y ∈ Z_towergraphE M ↔ y ∈ 𝔽 ∧ ∀ (x:M), ∃(z:M), triple x y z ∈ towergraphE M:=
  assume y,
  begin
    unfold Z_towergraphE,
    rw comprehension, 
  end 

lemma Z_towergraphE2_members: ∀ (y:M), y ∈ Z_towergraphE2 M ↔ 
y ∈ 𝔽  ∧ ∀ (x z w:M), (triple x y z ∈ towergraphE M 
∧ triple x y w ∈ towergraphE M → z = w) :=
 assume y,
  begin
    unfold Z_towergraphE2,
    rw comprehension, 
  end 

lemma Z_towerE_defined_members: ∀(y:M), y ∈ Z_towerE_defined M ↔
  y ∈ 𝔽 ∧ ∀(m:M), ∃(z:M), triple m y z ∈ towergraphE M:=
  assume y,
  begin
    unfold Z_towerE_defined,
    rw comprehension,
  end 

lemma Z_towerE_singlevalued_members: ∀(y:M), y ∈ Z_towerE_singlevalued M ↔
 y ∈ 𝔽  ∧ ∀ (m z w:M), triple m y z ∈ towergraphE M → triple m y w ∈ towergraphE M → z = w :=
  assume y,
  begin
    unfold Z_towerE_singlevalued,
    rw comprehension,
  end 

lemma towergraphE_members: ∀ (x y z:M), (triple x y z ∈ towergraphE M ↔ y ∈ 𝔽 ∧ 
∀ (Z:M), 
      (∀ (m:M), triple m zero m ∈ Z) ∧  
      (∀ (m y z:M), triple m y z ∈ Z →  (∃ u, u ∈ 𝕊 y) → triple m (𝕊 y) ( exp2 M z) ∈ Z)
      → triple x y z ∈ Z ):=
  assume x y z, 
  begin
   unfold towergraphE,
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

lemma towergraphE_members2: ∀ (u:M), u ∈ towergraphE M → ∃ (x y z:M), u = triple x y z:=
  assume u,
  begin
    intro h,
    unfold towergraphE at h,
    rw comprehension at h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    use x, use y, use z, 
    exact h5, 
  end

def tower (m y:M):= setof(λ u,∃ (z:M), triple m y z ∈ towergraphE M ∧ u ∈ z)
def φ (m:M):= setof(λ z,  ∃ (y:M), y ∈ 𝔽 ∧ z = tower M m y ∧ ∃ (u:M), u ∈ z) 
-- Note, φ contains the inhabited members of the range of tower(m,⬝)

def phi_members: ∀ (m z:M), z ∈ φ  M m ↔  ∃ (y:M), y ∈ 𝔽  ∧ z = tower M m y ∧ ∃ (u:M), u ∈ z:=
  assume m z,
  begin
    unfold φ,
    rw comprehension,
  end 
  
def f_sixpointeightE(m y:M) := setof(λ (t:M), ∃ (x u:M), t = ‹ x, u› ∧ x ≤ y ∧ u = tower M m x ∧ u ∈ 𝔽 ∧ x ∈ 𝔽 )

lemma  f_sixpointeightE_members:  ∀ (m y t:M), t ∈ f_sixpointeightE M m y ↔  ∃ (x u:M), t = ‹ x, u› ∧ x ≤ y ∧ u = tower M m x ∧ u ∈ 𝔽 ∧ x ∈ 𝔽 :=
  assume m y, 
  begin 
    unfold f_sixpointeightE,
    intro t, 
    rw comprehension, 
  end

lemma tower_members: ∀ (m y :M), u ∈ tower M m y  ↔ ∃(z:M), triple m y z ∈ towergraphE M ∧ u ∈ z:=
  assume z m,
  begin
    unfold tower,
    rw comprehension,      
  end 

def Z83E:M := setof(λ y, y ∈ 𝔽 ∧ ∀ (m z:M), triple m y z ∈ towergraphE M ↔ z = tower M m y)

lemma Z83E_members: ∀ (y:M), y ∈ Z83E M ↔ y ∈ 𝔽 ∧ ∀ (m z:M), triple m y z ∈ towergraphE M ↔ z = tower M m y:=
  assume y,
  begin
    unfold Z83E,
    rw comprehension, 
  end 

def Z86E(m:M):M := setof(λ y, y ∈ 𝔽 ∧  ((∃ u, u ∈ tower M m y) → tower M m y ∈ 𝔽 ))

lemma Z86E_members : ∀(m y:M), y ∈ Z86E M m ↔ y ∈ 𝔽 ∧ ( (∃ u, u ∈ tower M m y) → tower M m y ∈ 𝔽) :=
  assume m y,
  begin
    unfold Z86E,
    rw comprehension, 
  end

def ZIinNC(m:M):= setof(λ (y:M), y ∈ 𝔽 ∧ (m ∈ NC M → (∃ (u:M), u ∈ tower M m y) → tower M m y ∈ NC M))

lemma ZIinNC_members(m:M): ∀(y:M), y ∈ ZIinNC M m ↔ y ∈ 𝔽 ∧ (m ∈ NC M → (∃ (u:M), u ∈ tower M m y) → tower M m y ∈ NC M):=
  assume y,
  begin
    unfold ZIinNC,
    rw comprehension, 
  end

def Z87FE(m:M):M := setof(λ y, y ∈ 𝔽 ∧  ( m ∈ NC M  →  (∃ u, u ∈ tower M m y) → y ⪯ tower M m y))
lemma Z87FE_members : ∀(m y:M), y ∈ Z87FE M m ↔ y ∈ 𝔽 ∧ ( m ∈ NC M  →  (∃ u, u ∈ tower M m y) → y ⪯ tower M m y) :=
  assume m y,
  begin
    unfold Z87FE,
    rw comprehension, 
  end
  
lemma towergraphE_members1: Rel (towergraphE M):= 
  begin
    unfold Rel_definition, 
    intro u,
    unfold towergraphE,
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

lemma towergraph_membersE2: ∀ (u:M), u ∈ towergraphE M → ∃ (x y z:M), u = triple x y z:=
  assume u,
  begin
    intro h,
    unfold towergraphE at h,
    rw comprehension at h,
    cases h with x h2,
    cases h2 with y h3,
    cases h3 with z h4,
    cases h4 with h5 h6,
    use x, use y, use z, 
    exact h5, 
  end 

def Z_towerENC (m:M):= setof(λ y, y ∈ 𝔽  ∧  ((∃ u, u ∈ tower M m y) → tower M m y ∈ NC M ))
lemma Z_towerENC_members : ∀(m y:M), y ∈ Z_towerENC M m ↔ y ∈ 𝔽 ∧   ( (∃ u, u ∈ tower M m y) →  tower M m y ∈ NC M) :=
  assume m y,
  begin
    unfold Z_towerENC,
    rw comprehension, 
  end

lemma cantor: ∀ (x:M), ¬ similar M (USC x) (SC x):=
  begin
    intros x h,
    unfold similar at h,
    cases h with f h3,
    set D := setof(λ(t:M),t ∈ x ∧ ∃(y:M), ‹single t,y› ∈ f ∧ ¬ t ∈ y ) with Ddef,
    -- stratification t:0, x:1, y:1,  single t: 1 f:3
    have h4: D ∈ SC x:=
      begin
        rw sc_members,
        rw subset_definition,
        intros z hz,
        rw Ddef at hz,
        rw comprehension at hz,
        exact hz.1,
      end, 
    unfold similarity at h3,
    cases h3 with honeone honto,
    unfold onto at honto,
    have h5:= honto D h4,
    cases h5 with a h6,
    cases h6 with ha h7,
    rw usc at ha,
    cases ha with b h11,
    cases h11 with h12 h13,
    rw h13 at *,
    have h8: ¬ b ∈ D:=
      begin
        intros h9,
        rw Ddef at h9,
        rw comprehension at h9,
        cases h9 with h14 h15,
        cases h15 with u h16,
        cases h16 with h17 h18,
        have h19: u= D:= 
          begin
            unfold oneone at honeone,
            rcases honeone with ⟨ h30, h31, h32⟩,
            unfold maps at h30,
            rcases h30 with ⟨ h33, h34, h35, h36⟩,
            have h37:= h35 (single b) u D,
            apply h37,
            rw usc,
            split,
            {
              use b,
              simp,
              exact h14,
            },
            {
              exact ⟨ h17, h7⟩,
            }
          end,
        rw h19 at *,
        apply h18,
        rw Ddef,
        rw comprehension,
        split,
        {
          exact h14,
        },
        {
          use D,
          exact ⟨ h7, h18⟩,
        }
      end,
    have h20: b ∈ D:=
      begin
        rw Ddef,
        rw comprehension,
        split,
        {
          exact h12,
        },
        {
          use D,
          exact ⟨h7, h8⟩,
        }
      end,
    contradiction,
  end 

lemma cantor2: ∀ (x u:M), u ⊆ x → ¬ similar M (USC u) (SC x):=
  begin
    intros x u hux h,
    unfold similar at h,
    cases h with f h3,
    set D := setof(λ(t:M),t ∈ u ∧ ∃(y:M), ‹single t,y› ∈ f ∧ ¬ t ∈ y ) with Ddef,
    -- stratification t:0, u:1, x:1, y:1,  single t: 1 f:3
    have h4: D ∈ SC x:=
      begin
        rw sc_members,
        rw subset_definition,
        intros z hz,
        rw Ddef at hz,
        rw comprehension at hz,
        have h20:= hz.1,
        exact member_subset M u x z hux h20,
      end, 
    unfold similarity at h3,
    cases h3 with honeone honto,
    unfold onto at honto,
    have h5:= honto D h4,
    cases h5 with a h6,
    cases h6 with ha h7,
    rw usc at ha,
    cases ha with b h11,
    cases h11 with h12 h13,
    rw h13 at *,
    have h8: ¬ b ∈ D:=
      begin
        intros h9,
        rw Ddef at h9,
        rw comprehension at h9,
        cases h9 with h14 h15,
        cases h15 with u h16,
        cases h16 with h17 h18,
        have h19: u= D:= 
          begin
            unfold oneone at honeone,
            rcases honeone with ⟨ h30, h31, h32⟩,
            unfold maps at h30,
            rcases h30 with ⟨ h33, h34, h35, h36⟩,
            have h37:= h35 (single b) u D,
            apply h37,
            rw usc,
            split,
            {
              use b,
              simp,
              exact h14,
            },
            {
              exact ⟨ h17, h7⟩,
            }
          end,
        rw h19 at *,
        apply h18,
        rw Ddef,
        rw comprehension,
        split,
        {
          exact h14,
        },
        {
          use D,
          exact ⟨ h7, h18⟩,
        }
      end,
    have h20: b ∈ D:=
      begin
        rw Ddef,
        rw comprehension,
        split,
        {
          exact h12,
        },
        {
          use D,
          exact ⟨h7, h8⟩,
        }
      end,
    contradiction,
  end 


def Z_towerEstrictlyincreasing:= setof(λ (y:M), y ∈ 𝔽 ∧ ∀ (m:M), m ∈ NC M → (∃ (u:M), u ∈ tower M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y ⋖ tower M m y )

lemma Z_towerEstrictlyincreasing_members: ∀ (y:M), y ∈ Z_towerEstrictlyincreasing M ↔ 
 y ∈ 𝔽 ∧ ∀ (m:M), m ∈ NC M → (∃ (u:M), u ∈ tower M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y ⋖ tower M m y  :=
  assume y,
  begin
    unfold Z_towerEstrictlyincreasing,
    rw comprehension, 
  end

def Z_towerinNC(m:M):= setof(λ (y:M), y ∈ 𝔽 ∧ (m ∈ NC M → (∃ (u:M), u ∈ tower M m y) → tower M m y ∈ NC M))

lemma Z_towerinNC_members(m:M): ∀(y:M), y ∈ Z_towerinNC M m ↔ y ∈ 𝔽 ∧ (m ∈ NC M → (∃ (u:M), u ∈ tower M m y) → tower M m y ∈ NC M):=
  assume y,
  begin
    unfold Z_towerinNC,
    rw comprehension, 
  end

def ZsixpointfourE(m:M):M := setof(λ (y:M), y ∈ 𝔽 ∧ (tower M m y ∈ NC M →  m ⪯ tower M m y ))

lemma ZsixpointfourE_members(m:M): ∀ (y:M),  y ∈ ZsixpointfourE M m ↔  y ∈ 𝔽 ∧  (tower M m y ∈ NC M  →  m ⪯ tower M m y):=
  assume y,
  begin
    unfold ZsixpointfourE,
    rw comprehension,
  end 

def Z_towerup (p:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ((∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⋖ tower M p y))
lemma Z_towerup_members(p:M): ∀ (y:M), y ∈ Z_towerup M p ↔ y ∈ 𝔽 ∧ ((∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⋖ tower M p y):=
  begin
    intros y,
    unfold Z_towerup,
    rw comprehension,
  end

def Z_towerup2 (p:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ((∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⪯  tower M p y))
lemma Z_towerup2_members(p:M): ∀ (y:M), y ∈ Z_towerup2 M p ↔ y ∈ 𝔽 ∧ ((∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⪯  tower M p y):=
  begin
    intros y,
    unfold Z_towerup2,
    rw comprehension,
  end

def Z_towerorder:= setof(λ (y:M),  y ∈ 𝔽 ∧ ( ∀ (x m:M), x ∈ 𝔽 → m ∈ NC M → tower M m y ∈ NC M → x < y →  tower M m x ⋖  tower M m y))

lemma Z_towerorder_members: ∀ (y:M), y ∈ Z_towerorder M ↔
 y ∈ 𝔽 ∧ ( ∀ (x m:M), x ∈ 𝔽 → m ∈ NC M → tower M m y ∈ NC M → x < y →  tower M m x ⋖  tower M m y):=
  assume y,
  begin
    unfold Z_towerorder,
    rw comprehension, 
  end

def Z_TofI(n:M):= setof(λ(y:M), y ∈ 𝔽 ∧ (( ∃(u:M), u ∈ tower M n y) → 𝕋 M (tower M n y) = tower M (𝕋 M n) (𝕋 M y)))
lemma Z_TofI_members(n:M) : ∀(y:M), y ∈ Z_TofI M n ↔
y ∈ 𝔽 ∧ ( ( ∃(u:M), u ∈ tower M n y) → 𝕋 M (tower M n y) = tower M (𝕋 M n) (𝕋 M y)) :=
  begin
    intros y,
    unfold Z_TofI,
    rw comprehension,
  end  

def Z_TI(n:M):= setof(λ(y:M), y ∈ 𝔽 ∧ (( ∃(u:M), u ∈ 𝕀 M n y) → 𝕋 M (𝕀 M n y) = 𝕀 M (𝕋 M n) (𝕋 M y)))
lemma Z_TI_members(n:M) : ∀(y:M), y ∈ Z_TI M n ↔
y ∈ 𝔽 ∧ ( ( ∃(u:M), u ∈ 𝕀 M n y) → 𝕋 M (𝕀 M n y) = 𝕀 M (𝕋 M n) (𝕋 M y)) :=
  begin
    intros y,
    unfold Z_TI,
    rw comprehension,
  end  

def Z_towerbreakNC(n x:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ((∃(u:M),u ∈ tower M (tower M n x) y)→ x + y ∈ 𝔽 ∧ (tower M n (x+y)) = tower M (tower M n x) y))
lemma Z_towerbreakNC_members(n x:M): ∀(y:M), y ∈ Z_towerbreakNC M n x ↔ y ∈ 𝔽 ∧ ((∃(u:M),u ∈ tower M (tower M n x) y)→ x + y ∈ 𝔽 ∧ (tower M n (x+y)) = tower M (tower M n x) y):=
  begin
    intros y,
    unfold Z_towerbreakNC,
    rw comprehension,
  end

def Z_towerbreakNC2(n x:M):= setof(λ(y:M), y ∈ 𝔽 ∧ (((∃(u:M),u ∈ tower M n (x+y))→ x + y ∈ 𝔽 ∧ (tower M n (x+y)) = tower M (tower M n x) y)))
lemma Z_towerbreakNC2_members(n x:M): ∀(y:M), y ∈ Z_towerbreakNC2 M n x ↔ y ∈ 𝔽 ∧ ((∃(u:M),u ∈ tower  M n (x+y))→ x + y ∈ 𝔽 ∧ (tower M n (x+y)) = tower M (tower M n x) y):=
  begin
    intros y,
    unfold Z_towerbreakNC2,
    rw comprehension,
  end

def Z_towerbreakNC3(n x:M):= setof(λ(y:M), y ∈ 𝔽 ∧ (x∈ 𝔽 →   x + y ∈ 𝔽 → (tower M n (x+y)) = tower M (tower M n x) y))
lemma Z_towerbreakNC3_members(n x:M): ∀(y:M), y ∈ Z_towerbreakNC3 M n x ↔ y ∈ 𝔽 ∧ ( x∈ 𝔽 →  x + y ∈ 𝔽 → (tower M n (x+y)) = tower M (tower M n x) y):=
  begin
    intros y,
    unfold Z_towerbreakNC3,
    rw comprehension,
  end

def Z_towerbreakI2(n y:M):= setof(λ(z:M), z ∈ 𝔽 ∧  (y+z ∈ 𝔽 →  (𝕀 M n (y+z) = 𝕀 M (𝕀 M n y) z)))
lemma Z_towerbreakI2_members(n y:M): ∀(z:M), z ∈ Z_towerbreakI2 M n y ↔ z ∈ 𝔽 ∧  (y+z ∈ 𝔽 →  (𝕀 M n (y+z) = 𝕀 M (𝕀 M n y) z)):=
  begin
    intros z,
    unfold Z_towerbreakI2,
    rw comprehension,
  end
def Z_mylessthanImy(m:M):= setof(λ(y:M),y∈ 𝔽 ∧ ((¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → m+y ≤  𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽))
lemma Z_mylessthanImy_members(m:M): ∀(y:M), y ∈Z_mylessthanImy M m ↔ y∈ 𝔽 ∧ ( (¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → m+y ≤  𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽) :=  
  begin
    intros y,
    unfold Z_mylessthanImy,
    rw comprehension,
  end

def Z_letosum(x:M):= setof(λ(y:M), y ∈ 𝔽 ∧ (x ≤ y → ∃ (r:M), r ∈ 𝔽 ∧ x+r = y) )
lemma Z_letosum_members(x:M): ∀(y:M), y ∈ Z_letosum M x ↔ y ∈ 𝔽 ∧ (x ≤ y → ∃ (r:M), r ∈ 𝔽 ∧ x+r = y):=
  begin
    intros y,
    unfold Z_letosum,
    rw comprehension,
  end

def ftwopointsix (x:M):= setof(λ(p:M), ∃ (a:M), p = ‹single a, USC a› ∧ a ⊆ x  )
lemma ftwopointsix_members(x:M): ∀ (p:M), p ∈ ftwopointsix M x ↔   ∃ (a:M), p = ‹single a, USC a› ∧ a ⊆ x :=
  begin
    intros p,
    unfold ftwopointsix,
    rw comprehension,
  end

def Z_sevenpointone2 := setof(λ(k:M), k∈ 𝔽 ∧   ( ∀(m:M), m ∈ NC M → (∃(u v:M), u ∈ m ∧ v ∈ u) → k = Nc M (φ M (𝕋 M m)) → φ M m ∈ FINITE M))
lemma Z_sevenpointone2_members: ∀ (k:M), k ∈ Z_sevenpointone2 M  ↔ k ∈ 𝔽 ∧ (∀(m:M), m ∈ NC M → (∃(u v:M), u ∈ m ∧ v ∈ u) → k = Nc M (φ M (𝕋 M m)) → φ M m ∈ FINITE M):=
  begin 
    intros k,
    unfold Z_sevenpointone2,
    rw comprehension,
  end  

def Z_ylessdottower:= setof(λ(y:M), y ∈ 𝔽 ∧ (∀ (n:M), n ∈ NC M → zero ⋖ n →
(∃ (u:M), u ∈ tower M n y) → y ⋖ tower M n y))

lemma Z_ylessdottower_members: ∀ (y:M), y ∈ Z_ylessdottower M ↔
 y ∈ 𝔽 ∧ (∀ (n:M), (n ∈ NC M) → zero ⋖ n →
(∃ (u:M), u ∈ tower M n y) → y ⋖ tower M n y):=
  begin
    intros y,
    unfold Z_ylessdottower,
    rw comprehension,
  end

def Z_towersfinite (n:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ∃ (u:M), u = tower M n y )
lemma Z_towersfinite_members(n:M): ∀ (y:M), y ∈ Z_towersfinite M n ↔ y ∈ 𝔽 ∧ ∃(u:M), u = tower M n y:=
  begin
    intros y,
    unfold Z_towersfinite,
    rw comprehension,
  end

def Z_sixpointtwo2(m:M):= setof(λ (p:M), p ∈ 𝔽 ∧ (𝕊 p ∈ 𝔽 →  tower M m (𝕊 p) = (Λ:M)))
lemma Z_sixpointtwo2_members(m:M): ∀ ( p:M), p ∈ Z_sixpointtwo2 M m ↔  p ∈ 𝔽  ∧ (𝕊 p ∈ 𝔽 →  tower M m (𝕊 p) = (Λ:M)):=
  begin
    intros p,
    unfold Z_sixpointtwo2,
    rw comprehension,
  end 

def Z_offtheend2(n:M):= setof(λ(y:M), y ∈ 𝔽 ∧ ∀ (z:M),(z ∈ 𝔽 → z < y → tower M n z = Λ → tower M n y = Λ))
lemma Z_offtheend2_members(n:M): ∀(y:M), y ∈ Z_offtheend2 M n ↔  y ∈ 𝔽 ∧ ∀ (z:M),(z ∈ 𝔽 → z < y → tower M n z = Λ → tower M n y = Λ):=
  begin
    intros y,
    unfold Z_offtheend2,
    rw comprehension,
  end

def SpeckerX(κ:M):= setof(λ(z:M), z ∈ 𝔽 ∧ ∃ (n:M), n ∈ NC M ∧ z = Nc M (φ M n) ∧ κ ∈ φ M n)
lemma SpeckerX_members(κ:M): ∀(z:M), z ∈ SpeckerX M κ ↔  z ∈ 𝔽 ∧ ∃ (n:M), n ∈ NC M ∧ z = Nc M (φ M n) ∧ κ ∈ φ M n:=
  begin
    intros κ,
    unfold SpeckerX,
    rw comprehension,
  end

def Z_decidable(x:M):= setof(λ(t:M), t ∈ x ∨ ¬ t ∈ x)
lemma Z_decidable_members(x:M): ∀(t:M), t ∈ Z_decidable M x ↔ t ∈ x ∨ ¬ t ∈ x:=
  begin
    intros t,
    unfold Z_decidable,
    rw comprehension,
  end 

def Z_mplusmleexpm:= setof(λ (m:M), m ∈ 𝔽 ∧ ( exp M m ∈ 𝔽 →  m+m ≤ exp M m)) 
lemma Z_mplusmleexpm_members: ∀ (m:M), m ∈ Z_mplusmleexpm M ↔ m ∈ 𝔽 ∧ (exp M m ∈ 𝔽 → m+m ≤ exp M m):=  
  begin
    intros m,
    unfold Z_mplusmleexpm,
    rw comprehension,
  end

def Z_Iorder2 (n m:M):= setof(λ (y:M), y ∈ 𝔽 ∧ ( 𝕀 M m y ∈ 𝔽 → 𝕀 M n y < 𝕀 M m y))
lemma Z_Iorder2_members: ∀(n m y:M), y ∈ Z_Iorder2 M n m ↔  y ∈ 𝔽 ∧ (𝕀 M m y ∈ 𝔽 → 𝕀 M n y < 𝕀 M m y):=
  begin
    intros n m y,
    unfold Z_Iorder2,
    rw comprehension,
  end

def freverse (n m:M) := setof(λ (z:M), ∃ (p q:M), z = ‹p,q›  ∧ ∃ (y:M), y ∈ 𝔽 ∧ p = 𝕀 M m y ∧ q = 𝕀 M n y ∧ p ∈ Φ M m )
lemma freverse_members: ∀ (n m z:M), z ∈ freverse M n m ↔ 
∃ (p q:M), z = ‹p,q›  ∧ ∃ (y:M), y ∈ 𝔽 ∧ p = 𝕀 M m y ∧ q = 𝕀 M n y ∧ p ∈ Φ M m :=
  begin
    intros n m z,
    unfold freverse,
    rw comprehension,
  end

def Z_Phibound (m n:M) := setof (λ(y:M),y ∈ 𝔽 ∧ ( (∃ (u:M), u ∈ 𝕀 M n y) → 
Nc M (Φ M (𝕀 M n y)) + 𝕋 M (𝕋 M y) = Nc M (Φ M n)))
lemma Z_Phibound_members: ∀ (m n y:M),
y ∈ Z_Phibound M m n ↔ y ∈ 𝔽 ∧ (  (∃ (u:M), u ∈ 𝕀 M n y) → 
Nc M (Φ M (𝕀 M n y)) + 𝕋 M (𝕋 M y) = Nc M (Φ M n)):=
  begin
    intros m n y,
    unfold Z_Phibound,
    rw comprehension,
  end

def gNbound:= setof(λ(p:M), ∃ (a b:M), p = ‹a,b› ∧ a ∈ 𝔽 ∧  𝕀 M one a = b ∧ b ∈ Φ M one)
lemma gNbound_members: ∀ (p:M), p ∈ gNbound M↔  ∃ (a b:M), p = ‹a,b› ∧ a ∈ 𝔽 ∧  𝕀 M one a = b ∧ b ∈ Φ M one:=
  begin
   intros p,
   unfold gNbound,
   rw comprehension,
  end

def Z_lessthansum:= setof(λ(q:M), q ∈ 𝔽 ∧ (∀(n p:M), n ∈ 𝔽 → p ∈ 𝔽 → n= p+ q → zero < q → p < n ))
lemma Z_lessthansum_members: ∀(q:M), q ∈ Z_lessthansum M ↔  q ∈ 𝔽 ∧ (∀(n p:M), n ∈ 𝔽 → p ∈ 𝔽 → n= p+ q → zero < q → p < n) :=
  begin
    intros q,
    unfold Z_lessthansum,
    rw comprehension, 
  end

def Z_ILambda:= setof(λ(t:M), t ∈ 𝔽 ∧ 𝕀 M Λ t = Λ)
lemma Z_ILambda_members: ∀ (t:M), t ∈ Z_ILambda M ↔  t ∈ 𝔽 ∧ 𝕀 M Λ t = Λ:=
  begin
    intros t,
    unfold Z_ILambda,
    rw comprehension,
  end

def FC (t:M):= Ap (inv (ChurchFrege M)) t

def Z_FCmaps:= setof(λ(x:M), x ∈ 𝔽 ∧  ∃(y:M),‹y,x › ∈ ChurchFrege M
∧ ∀ (z:M), ‹z,x› ∈ ChurchFrege M → z = y)
lemma Z_FCmaps_members:∀(x:M), x ∈ Z_FCmaps M ↔ x ∈ 𝔽 ∧ ∃(y:M),‹y,x › ∈ ChurchFrege M
∧ ∀ (z:M), ‹z,x› ∈ ChurchFrege M → z = y:=
  begin
    intros x,
    unfold Z_FCmaps,
    rw comprehension,
  end

def Z_FCmaps2:= setof(λ(x:M), x ∈ 𝔽 ∧  ‹FC M x,x › ∈ ChurchFrege M )
lemma Z_FCmaps2_members: ∀(x:M), x ∈ Z_FCmaps2 M ↔ x ∈ 𝔽 ∧  ‹FC M x,x › ∈ ChurchFrege M:=
  begin
    intros x,
    unfold Z_FCmaps2,
    rw comprehension,
  end

def Z_FCplus:= setof(λ(y:M), y ∈ 𝔽 ∧ ∀(x:M),x ∈ 𝔽 → x + y ∈ 𝔽 → FC M (x+y) = (FC M x) ⊕ (FC M y))
lemma Z_FCplus_members: ∀(y:M),y ∈ Z_FCplus M ↔  y ∈ 𝔽 ∧ ∀(x:M),x ∈ 𝔽 → x + y ∈ 𝔽 → FC M (x+y) = (FC M x) ⊕ (FC M y):=
  begin
    intros y,
    unfold Z_FCplus,
    rw comprehension,
  end
  
def Z_FCinitial (k n:M):= setof(λ(x:M), x ∈ 𝔽 ∧  
∀ (q:M), q = FC M x → 
∀ (p:M), p ∈ ℕℕ → p ≺ q → ∃(y:M), y ∈ 𝔽 ∧ 
FC M y = p
)

lemma Z_FCinitial_members: ∀ (k n x:M), x ∈ Z_FCinitial M k n ↔ 
x ∈ 𝔽 ∧ ∀ (q:M), q = FC M x → 
∀ (p:M), p ∈ ℕℕ → p ≺ q → ∃(y:M), y ∈ 𝔽 ∧ 
FC M y = p :=
  begin
    intros k n x,
    unfold Z_FCinitial,
    rw comprehension,
  end

def W_precmaximal (k n:M):= setof(λ(X:M), X ∈ FINITE M ∧  ((∃(u:M), u ∈ X) → X ⊆ ℕℕ →
∃ (m:M), m ∈ X ∧ ∀ (x:M), x ∈ X → x ≼ m ))
lemma W_precmaximal_members: ∀(k n X:M), X ∈ W_precmaximal M k n ↔  X ∈ FINITE M ∧  ((∃(u:M), u ∈ X) → X ⊆ ℕℕ →
∃ (m:M), m ∈ X ∧ ∀ (x:M), x ∈ X → x ≼ m):=
  begin
    intros k n X,
    unfold W_precmaximal,
    rw comprehension,
  end

def CF (k n:M):= setof(λ(z:M), ∃ (p q:M), z = ‹p,q› ∧ q = 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero))))))) 
lemma CF_members : ∀ (k n z:M), z ∈ CF M k n ↔ 
∃ (p q:M), z = ‹p,q› ∧ q = 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))):=
  begin
    intros k n z,
    split,
    {
      intros h,
      unfold CF at h,
      rw comprehension at h,
      exact h,
    },
    { 
      intros h,
      unfold CF,
      rw comprehension,
      exact h,
    }
  end

def Z_ChurchToFrege(k n:M):=  setof(λ (p:M), p ∈ ℕℕ ∧  
-- \T^6 p \SF\ \zero \in \F
𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) ∈ 𝔽 ∧
-- \FC (\T^6 (p \SF\ \zero)) = p 
FC M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero))))))) = p ∧
-- \forall x( x ∈F → x  < \T^6 (p\SF\ \zero)\,\exists q \prec p\, \T^6 (q\SF\ \zero) = x)
∀ (x:M),x ∈ 𝔽 → x <  𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) → 
∃ (q:M), q ≺ p ∧ 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap q succ) zero)))))) = x 
)

lemma Z_ChurchToFrege_members: ∀ (k n p:M), 
p ∈ Z_ChurchToFrege M k n ↔ p ∈ ℕℕ ∧ 
𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) ∈ 𝔽 ∧
FC M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero))))))) = p ∧
∀ (x:M),x ∈ 𝔽 → x <  𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) → 
∃ (q:M), q ≺ p ∧ 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap q succ) zero)))))) = x :=
  begin
    intros k n p,
    unfold Z_ChurchToFrege,
    rw comprehension,
  end


#axioms_all