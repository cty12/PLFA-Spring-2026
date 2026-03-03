namespace PolyCoercions

-- Represents the raw types in our system.
inductive Ty : Type
  | nat : Ty
  | dyn : Ty
  | tvar : Nat → Ty
  | fn : Ty → Ty → Ty
  | univ : Ty → Ty

abbrev Rename := Nat → Nat
abbrev TySubst := Nat → Ty

-------------------------------------------------------------------------------
-- TYPE SUBSTITUTION (Types into Types)
-------------------------------------------------------------------------------

def extTy (ρ : Rename) : Rename
  | 0     => 0
  | i + 1 => (ρ i) + 1

def renameTy (ρ : Rename) : Ty → Ty
  | .tvar X   => .tvar (ρ X)
  | .nat      => .nat
  | .dyn      => .dyn
  | .fn A B   => .fn (renameTy ρ A) (renameTy ρ B)
  | .univ A   => .univ (renameTy (extTy ρ) A)

def liftTy (A : Ty) : Ty := renameTy (fun i => i + 1) A

def extsTy (σ : TySubst) : TySubst
  | 0     => .tvar 0
  | X + 1 => liftTy (σ X)

def substTy (σ : TySubst) : Ty → Ty
  | .tvar X   => σ X
  | .nat      => .nat
  | .dyn      => .dyn
  | .fn A B   => .fn (substTy σ A) (substTy σ B)
  | .univ A   => .univ (substTy (extsTy σ) A)

/-- Substitutes a type `B` for the type variable `0` inside a type `A`, 
    decrementing all other free type variables. 
    (Used for type-level beta reduction if you ever add type operators, 
    or when evaluating type applications in typing rules). -/
def singleSubstTy (A : Ty) (B : Ty) : Ty :=
  substTy (fun i => match i with
    | 0     => B
    | j + 1 => .tvar j) A

-------------------------------------------------------------------------------
-- WELL-FORMED TYPES
-------------------------------------------------------------------------------

/-- WfTy Δ A means that all free type variables in A are < Δ -/
inductive WfTy : Nat → Ty → Prop where
  | wf_tvar {Δ X : Nat} : X < Δ → WfTy Δ (.tvar X)
  | wf_nat  {Δ : Nat}   : WfTy Δ .nat
  | wf_dyn  {Δ : Nat}   : WfTy Δ .dyn
  | wf_fn   {Δ : Nat} {A B : Ty} : WfTy Δ A → WfTy Δ B → WfTy Δ (.fn A B)
  | wf_univ {Δ : Nat} {A : Ty}   : WfTy (Δ + 1) A → WfTy Δ (.univ A)

-- Ground types for the dynamic type injections/projections[cite: 94].
inductive Grnd : Type
  | fn : Grnd   -- ★ ⇒ ★
  | nat : Grnd   -- `ℕ
  | tvar : Nat → Grnd -- ` X

-- Helper to convert a ground type back into a standard type[cite: 95].
def Grnd.toTy : Grnd → Ty
  | fn => .fn .dyn .dyn
  | nat => .nat
  | tvar x => .tvar x

-------------------------------------------------------------------------------
-- TYPE VARIABLE BINDING ENVIRONMENT
-------------------------------------------------------------------------------

-- A typing environment mapping type variables (by index) to Types
abbrev Env := List (Nat × Ty)

-- Looks up a bound variable in the context (`Σ ∋ X := A` in Agda)
def lookup (env : Env) (x : Nat) (A : Ty) : Prop :=
  (x, A) ∈ env

-- Applies a renaming function to both the indices and the types in the environment
def renameEnv (rho : Nat → Nat) (env : Env) : Env :=
  env.map (fun (x, A) => (rho x, renameTy rho A))

-- Lifts the entire environment by 1 (`⤊ Σ` in Agda)
def lift (env : Env) : Env :=
  renameEnv (fun x => x + 1) env

-------------------------------------------------------------------------------
-- TYPE PRECISION
-------------------------------------------------------------------------------

inductive TypePrecision : Nat → Env → Ty → Ty → Type

  -- ℕ ⊑ ℕ
  | nat_prec_nat {numTyVars : Nat} {env : Env} :
      TypePrecision numTyVars env .nat .nat

  -- X ⊑ X
  | var_prec_var {numTyVars : Nat} {env : Env} {X : Nat} :
      TypePrecision numTyVars env (.tvar X) (.tvar X)

  -- ★ ⊑ ★
  | dyn_prec_dyn {numTyVars : Nat} {env : Env} :
      TypePrecision numTyVars env .dyn .dyn

  -- ★ ⊑ X (όταν το X είναι δεσμευμένο στο ★)
  | dyn_prec_var {numTyVars : Nat} {env : Env} {X : Nat} :
      lookup env X .dyn →
      TypePrecision numTyVars env .dyn (.tvar X)

  -- ★ ⊑ ℕ
  | dyn_prec_nat {numTyVars : Nat} {env : Env} :
      TypePrecision numTyVars env .dyn .nat

  -- ★ ⊑ A ⇒ B
  | dyn_prec_fn {numTyVars : Nat} {env : Env} {A B : Ty} :
      TypePrecision numTyVars env .dyn A →
      TypePrecision numTyVars env .dyn B →
      TypePrecision numTyVars env .dyn (.fn A B)

  -- A ⇒ B ⊑ C ⇒ D
  | fn_prec_fn {numTyVars : Nat} {env : Env} {A B C D : Ty} :
      TypePrecision numTyVars env A C →
      TypePrecision numTyVars env B D →
      TypePrecision numTyVars env (.fn A B) (.fn C D)

  -- ∀ A ⊑ ∀ B
  | univ_prec_univ {numTyVars : Nat} {env : Env} {A B : Ty} :
      TypePrecision (numTyVars + 1) (lift env) A B →
      TypePrecision numTyVars env (.univ A) (.univ B)

  -- A ⊑ ∀ B
  | prec_univ {numTyVars : Nat} {env : Env} {A B : Ty} :
      TypePrecision (numTyVars + 1) ((0, Ty.dyn) :: lift env) (liftTy A) B →
      TypePrecision numTyVars env A (.univ B)

-------------------------------------------------------------------------------
-- Consistent Subtyping Relation
-------------------------------------------------------------------------------

-- Consistent Subtyping Relation
inductive ConsistentSubtyping : Nat → Env → Ty → Ty → Type

  -- ℕ ≲ ℕ
  | nat_sub_nat {numTyVars : Nat} {env : Env} :
      ConsistentSubtyping numTyVars env .nat .nat
      
  -- X ≲ X
  | var_sub_var {numTyVars : Nat} {env : Env} {X : Nat} :
      ConsistentSubtyping numTyVars env (.tvar X) (.tvar X)

  -- ★ ≲ ★
  | dyn_sub_dyn {numTyVars : Nat} {env : Env} :
      ConsistentSubtyping numTyVars env .dyn .dyn

  -- ★ ≲ X (when X is bound to ★)
  | dyn_sub_var {numTyVars : Nat} {env : Env} {X : Nat} :
      lookup env X .dyn →
      ConsistentSubtyping numTyVars env .dyn (.tvar X)

  -- X ≲ ★ (when X is bound to ★)
  | var_sub_dyn {numTyVars : Nat} {env : Env} {X : Nat} :
      lookup env X .dyn →
      ConsistentSubtyping numTyVars env (.tvar X) .dyn

  -- ★ ≲ ℕ
  | dyn_sub_nat {numTyVars : Nat} {env : Env} :
      ConsistentSubtyping numTyVars env .dyn .nat

  -- ℕ ≲ ★
  | nat_sub_dyn {numTyVars : Nat} {env : Env} :
      ConsistentSubtyping numTyVars env .nat .dyn

  -- A ⇒ B ≲ ★
  | fn_sub_dyn {numTyVars : Nat} {env : Env} {A B : Ty} :
      ConsistentSubtyping numTyVars env .dyn A →
      ConsistentSubtyping numTyVars env B .dyn →
      ConsistentSubtyping numTyVars env (.fn A B) .dyn

  -- ★ ≲ A ⇒ B
  | dyn_sub_fn {numTyVars : Nat} {env : Env} {A B : Ty} :
      ConsistentSubtyping numTyVars env A .dyn →
      ConsistentSubtyping numTyVars env .dyn B →
      ConsistentSubtyping numTyVars env .dyn (.fn A B) -- [cite: 4, 5]

  -- A ⇒ B ≲ C ⇒ D
  | fn_sub_fn {numTyVars : Nat} {env : Env} {A B C D : Ty} :
      ConsistentSubtyping numTyVars env C A →
      ConsistentSubtyping numTyVars env B D →
      ConsistentSubtyping numTyVars env (.fn A B) (.fn C D)

  -- ∀ A ≲ ∀ B
  | univ_sub_univ {numTyVars : Nat} {env : Env} {A B : Ty} :
      ConsistentSubtyping (numTyVars + 1) (lift env) A B →
      ConsistentSubtyping numTyVars env (.univ A) (.univ B) -- [cite: 5, 6]

  -- A ≲ ∀ B
  | sub_univ {numTyVars : Nat} {env : Env} {A B : Ty} :
      ConsistentSubtyping (numTyVars + 1) (lift env) (liftTy A) B →
      ConsistentSubtyping numTyVars env A (.univ B)

  -- ∀ A ≲ B
  | univ_sub {numTyVars : Nat} {env : Env} {A B : Ty} :
      ConsistentSubtyping (numTyVars + 1) ((0, Ty.dyn) :: lift env) A (liftTy B) →
      ConsistentSubtyping numTyVars env (.univ A) B

-------------------------------------------------------------------------------
-- COERCIONS
-------------------------------------------------------------------------------

-- The raw syntax of coercions, completely decoupled from their typing.
inductive Coercion : Type
  | id : Coercion
  | fn : Coercion → Coercion → Coercion     -- _ ↦ _
  | seq : Coercion → Coercion → Coercion     -- _ ⨟ _
  | forall_ : Coercion → Coercion            -- `∀_
  | gen : Coercion → Coercion                -- 𝒢
  | inst : Coercion → Coercion               -- ℐ
  | seal_ : Nat → Coercion                 -- _ -
  | unseal_ : Nat → Coercion                   -- _ +
  | inj : Grnd → Coercion                    -- _ !
  | proj : Grnd → Coercion                   -- _ `?

-- Notice that Nat and Env are now on the right side of the colon
inductive CoercTyping : Nat → Env → Coercion → Ty → Ty → Prop
  
  -- Identity
  | id {numTyVars : Nat} {env : Env} {A : Ty} : 
      CoercTyping numTyVars env Coercion.id A A
      
  -- Function Coercion
  | fn {numTyVars : Nat} {env : Env} {A B C D : Ty} {c d : Coercion} :
      CoercTyping numTyVars env c C A →
      CoercTyping numTyVars env d B D →
      CoercTyping numTyVars env (Coercion.fn c d) (.fn A B) (.fn C D)
      
  -- Sequencing
  | seq {numTyVars : Nat} {env : Env} {A B C : Ty} {c d : Coercion} :
      CoercTyping numTyVars env c A B →
      CoercTyping numTyVars env d B C →
      CoercTyping numTyVars env (Coercion.seq c d) A C
      
  -- Forall
  | forall_ {numTyVars : Nat} {env : Env} {A B : Ty} {c : Coercion} :
      CoercTyping (numTyVars + 1) (lift env) c A B →
      CoercTyping numTyVars env (Coercion.forall_ c) (.univ A) (.univ B)
      
  -- Generalize
  | gen {numTyVars : Nat} {env : Env} {A B : Ty} {c : Coercion} :
      CoercTyping (numTyVars + 1) (lift env) c (liftTy A) B →
      CoercTyping numTyVars env (Coercion.gen c) A (.univ B)
      
  -- Instantiate
  | inst {numTyVars : Nat} {env : Env} {A B : Ty} {c : Coercion} :
      CoercTyping (numTyVars + 1) ((0, Ty.dyn) :: lift env) c A (liftTy B) →
      CoercTyping numTyVars env (Coercion.inst c) (.univ A) B
      
  -- Seal
  | seal_ {numTyVars : Nat} {env : Env} {A : Ty} {X : Nat} :
      lookup env X A →
      CoercTyping numTyVars env (Coercion.seal_ X) A (.tvar X)
      
  -- Unseal
  | unseal_ {numTyVars : Nat} {env : Env} {A : Ty} {X : Nat} :
      lookup env X A →
      CoercTyping numTyVars env (Coercion.unseal_ X) (.tvar X) A
      
  -- Inject into Dynamic
  | inj {numTyVars : Nat} {env : Env} {G : Grnd} :
      CoercTyping numTyVars env (Coercion.inj G) (Grnd.toTy G) Ty.dyn
      
  -- Project from Dynamic
  | proj {numTyVars : Nat} {env : Env} {H : Grnd} :
      CoercTyping numTyVars env (Coercion.proj H) Ty.dyn (Grnd.toTy H)

-------------------------------------------------------------------------------
-- COMPILE CONSISTENT SUBTYPING TO COERCIONS
-------------------------------------------------------------------------------

def toCoercion {numTyVars : Nat} (env : Env) {A B : Ty} : 
  ConsistentSubtyping numTyVars env A B → Coercion

  | .nat_sub_nat => .id
  | .var_sub_var => .id
  | .dyn_sub_dyn => .id

  -- Variables to/from Dynamic map to seal/unseal.
  -- The `no` branches from Agda are unreachable here.
  | .dyn_sub_var (X := X) _ => .seal_ X
  | .var_sub_dyn (X := X) _ => .unseal_ X

  | .dyn_sub_nat => .proj .nat
  | .nat_sub_dyn => .inj .nat

  -- ⇒≲⇒ : (A ≲ C) ↦ (B ≲ D)
  | .fn_sub_fn hC hD => 
      .fn (toCoercion env hC) (toCoercion env hD)

  -- ⇒≲★ : ((A ≲ ★) ↦ (B ≲ ★)) ⨟ (★⇒★ !)
  | .fn_sub_dyn hC hD => 
      .seq (.fn (toCoercion env hC) (toCoercion env hD)) (.inj .fn)

  -- ★≲⇒ : (★⇒★ `?) ⨟ ((★ ≲ A) ↦ (★ ≲ B))
  | .dyn_sub_fn hC hD => 
      .seq (.proj .fn) (.fn (toCoercion env hC) (toCoercion env hD))

  -- ∀≲∀ : `∀ (≲-⇒ (⤊ Σ) A≲B)
  | .univ_sub_univ h => 
      .forall_ (toCoercion (lift env) h)

  -- ≲∀ : 𝒢 (≲-⇒ (⤊ Σ) A≲B)
  | .sub_univ h => 
      .gen (toCoercion (lift env) h)

  -- ∀≲ : ℐ (≲-⇒ ((Zᵗ , ★) ∷ ⤊ Σ) A≲B)
  | .univ_sub h => 
      .inst (toCoercion ((0, Ty.dyn) :: lift env) h)

-------------------------------------------------------------------------------
-- REVEAL AND CONCEAL COERCIONS
-------------------------------------------------------------------------------

-- A small helper to check if a type variable index is bound in the current environment
def isBound (env : Env) (X : Nat) : Bool :=
  env.any (fun (Y, _) => Y == X)

mutual
  /-- Generates a coercion from B to σ(B) -/
  def reveal (env : Env) : Ty → Coercion
    | .nat => .id
    | .dyn => .id
    | .tvar X => 
        if isBound env X then 
          .unseal_ X 
        else 
          .id
    | .fn A B => 
        .fn (conceal env A) (reveal env B)
    | .univ B => 
        .forall_ (reveal (lift env) B)

  /-- Generates a coercion from σ(B) to B -/
  def conceal (env : Env) : Ty → Coercion
    | .nat => .id
    | .dyn => .id
    | .tvar X => 
        if isBound env X then 
          .seal_ X 
        else 
          .id
    | .fn A B => 
        .fn (reveal env A) (conceal env B)
    | .univ B => 
        .forall_ (conceal (lift env) B)
end -- mutual

/-- 
  Lifting an environment maps `liftTy` over the bound types, 
  but leaves the term variable IDs (x) unchanged.
-/

theorem lookup_lift {env : Env} {x : Nat} {T : Ty}
  (h : lookup env x T) : 
  lookup (lift env) (x + 1) (liftTy T) := by
  -- lift env maps (y, A) to (y + 1, liftTy A). 
  -- We just apply the list mapping membership lemma directly to h.
  exact List.mem_map_of_mem h

-- 1. Helper Lemmas for Renaming Composition
theorem extTy_comp (ρ1 ρ2 : Rename) : 
  (fun x => extTy ρ1 (extTy ρ2 x)) = extTy (fun x => ρ1 (ρ2 x)) := by
  funext x
  cases x with
  | zero => rfl
  | succ n => rfl

theorem renameTy_comp (T : Ty) (ρ1 ρ2 : Rename) : 
  renameTy ρ1 (renameTy ρ2 T) = renameTy (fun x => ρ1 (ρ2 x)) T := by
  induction T generalizing ρ1 ρ2 with
  | nat => rfl
  | dyn => rfl
  | tvar x => rfl
  | fn A B ihA ihB =>
    calc renameTy ρ1 (renameTy ρ2 (.fn A B))
      _ = .fn (renameTy ρ1 (renameTy ρ2 A)) (renameTy ρ1 (renameTy ρ2 B)) := rfl
      _ = .fn (renameTy (fun x => ρ1 (ρ2 x)) A) (renameTy (fun x => ρ1 (ρ2 x)) B) := by rw [ihA, ihB]
      _ = renameTy (fun x => ρ1 (ρ2 x)) (.fn A B) := rfl
  | univ A ih =>
    calc renameTy ρ1 (renameTy ρ2 (.univ A))
      _ = .univ (renameTy (extTy ρ1) (renameTy (extTy ρ2) A)) := rfl
      _ = .univ (renameTy (fun x => extTy ρ1 (extTy ρ2 x)) A) := by rw [ih]
      _ = .univ (renameTy (extTy (fun x => ρ1 (ρ2 x))) A) := by 
            have h_ext := extTy_comp ρ1 ρ2
            rw [h_ext]
      _ = renameTy (fun x => ρ1 (ρ2 x)) (.univ A) := rfl

-- 2. Environment Commutativity (Lifting past a Renaming)
theorem renameEnv_ext_lift (ρ : Rename) (env : Env) :
  renameEnv (extTy ρ) (lift env) = lift (renameEnv ρ env) := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with | mk x T =>
    calc renameEnv (extTy ρ) (lift (⟨x, T⟩ :: tl))
      _ = renameEnv (extTy ρ) (⟨x + 1, renameTy (fun i => i + 1) T⟩ :: lift tl) := rfl
      _ = ⟨extTy ρ (x + 1), renameTy (extTy ρ) (renameTy (fun i => i + 1) T)⟩ :: renameEnv (extTy ρ) (lift tl) := rfl
      _ = ⟨ρ x + 1, renameTy (fun i => i + 1) (renameTy ρ T)⟩ :: renameEnv (extTy ρ) (lift tl) := by
            have h : renameTy (extTy ρ) (renameTy (fun i => i + 1) T) = renameTy (fun i => i + 1) (renameTy ρ T) := by
              rw [renameTy_comp, renameTy_comp]
              rfl
            rw [h]
            rfl
      _ = ⟨ρ x + 1, renameTy (fun i => i + 1) (renameTy ρ T)⟩ :: lift (renameEnv ρ tl) := by rw [ih]
      _ = lift (⟨ρ x, renameTy ρ T⟩ :: renameEnv ρ tl) := rfl
      _ = lift (renameEnv ρ (⟨x, T⟩ :: tl)) := rfl

theorem renameTy_ext_lift (ρ : Rename) (A : Ty) :
  renameTy (extTy ρ) (liftTy A) = liftTy (renameTy ρ A) := by
  calc renameTy (extTy ρ) (liftTy A)
    _ = renameTy (extTy ρ) (renameTy (fun i => i + 1) A) := rfl
    _ = renameTy (fun i => extTy ρ (i + 1)) A := by rw [renameTy_comp]
    _ = renameTy (fun i => ρ i + 1) A := rfl
    _ = renameTy (fun i => i + 1) (renameTy ρ A) := by rw [renameTy_comp]
    _ = liftTy (renameTy ρ A) := rfl

-- 3. Generalized Renaming Theorem for TypePrecision
noncomputable def rename_type_prec {numTyVars : Nat} {env : Env} {A B : Ty} (ρ : Rename)
  (h : TypePrecision numTyVars env A B) :
  ∀ {numTyVars'}, TypePrecision numTyVars' (renameEnv ρ env) (renameTy ρ A) (renameTy ρ B) := by
  induction h generalizing ρ with
  | nat_prec_nat => intros; exact .nat_prec_nat
  | var_prec_var => intros; exact .var_prec_var
  | dyn_prec_dyn => intros; exact .dyn_prec_dyn
  | dyn_prec_var h_lookup => 
      intros numTyVars'
      apply TypePrecision.dyn_prec_var
      -- Lean 4 infers the mapping function automatically, so we just pass h_lookup
      exact List.mem_map_of_mem h_lookup
  | dyn_prec_nat => intros; exact .dyn_prec_nat
  | dyn_prec_fn h1 h2 ih1 ih2 => 
      intros numTyVars'
      exact .dyn_prec_fn (ih1 ρ) (ih2 ρ)
  | fn_prec_fn h1 h2 ih1 ih2 => 
      intros numTyVars'
      exact .fn_prec_fn (ih1 ρ) (ih2 ρ)
  | univ_prec_univ h ih => 
      intros numTyVars'
      apply TypePrecision.univ_prec_univ
      have h_ih := ih (extTy ρ) (numTyVars' := numTyVars' + 1)
      rw [renameEnv_ext_lift] at h_ih
      exact h_ih
  | prec_univ h ih =>
      intros numTyVars'
      apply TypePrecision.prec_univ
      -- Rewrite the goal backwards using our lifting lemmas
      rw [← renameEnv_ext_lift, ← renameTy_ext_lift]
      -- Lean's `exact` tactic will now automatically see that the hypothesis
      -- is definitionally equal to the goal (evaluating the list map for us)
      have h_ih := ih (extTy ρ) (numTyVars' := numTyVars' + 1)
      exact h_ih

-- Lifting preserves type precision
noncomputable def lift_type_prec {numTyVars : Nat} {env : Env} {A A' : Ty}
  (hPrec : TypePrecision numTyVars env A A') : 
  TypePrecision (numTyVars + 1) (lift env) (liftTy A) (liftTy A') := by
  -- Note: hEnv is intentionally ignored here since type precision 
  -- depends strictly on the primary environment context `env1`.
  exact rename_type_prec (fun i => i + 1) hPrec

-- Environment Precision Relation
-- EnvPrecision numTyVars env1 env2 means env1 ⊑ env2
inductive EnvPrecision : Nat → Env → Env → Prop

  -- The empty environment is precise to the empty environment
  | nil {numTyVars : Nat} :
      EnvPrecision numTyVars [] []

  -- If env1 ⊑ env2, and type A ⊑ B, we can extend both environments 
  -- with the same variable X bound to A and B respectively.
  | cons {numTyVars : Nat} {env1 env2 : Env} {X : Nat} {A B : Ty} :
      EnvPrecision numTyVars env1 env2 →
      TypePrecision numTyVars env1 A B →
      EnvPrecision numTyVars ((X, A) :: env1) ((X, B) :: env2)

  -- Allow extending ONLY the left environment with a .dyn binding
  | cons_left_dyn {numTyVars : Nat} {env1 env2 : Env} {X : Nat} :
      EnvPrecision numTyVars env1 env2 →
      EnvPrecision numTyVars ((X, Ty.dyn) :: env1) env2

-- Lifting preserves environment precision
theorem lift_env_prec {numTyVars : Nat} {env1 env2 : Env}
  (h : EnvPrecision numTyVars env1 env2) : 
  EnvPrecision (numTyVars + 1) (lift env1) (lift env2) := by
  induction h with
  | nil => 
      -- lift [] is [], so the nil constructor trivially applies
      exact .nil
  | cons h_env h_prec ih =>
      -- By definition, lift ((X, A) :: env) evaluates to (X + 1, liftTy A) :: lift env.
      -- So we apply the cons constructor, which requires the lifted environment precision (our IH)
      -- and the lifted type precision (which we get from the previous lemma).
      apply EnvPrecision.cons
      · exact ih
      · exact lift_type_prec h_prec

  | cons_left_dyn h_env => sorry

/-- Predicate identifying leaf/atomic coercions that rely on TypePrecision. -/
inductive IsAtomic : Coercion → Prop where
  | id       : IsAtomic .id
  | inj  G   : IsAtomic (.inj G)
  | proj H   : IsAtomic (.proj H)
  | seal X   : IsAtomic (.seal_ X)
  | unseal X : IsAtomic (.unseal_ X)

inductive CoercPrecision : Nat → Env → Env → Coercion → Ty → Ty → Coercion → Ty → Ty → Prop where

  /-- Left-side Atomic: Handles IsAtomic c1 ⊑ (any non-sequence c2). -/
  | atomic_prec_l {numTyVars env_psi env1 env2 c1 c2 A B A' B'} :
      IsAtomic c1 → 
      (∀ c3 c4, c2 ≠ .seq c3 c4) → 
      TypePrecision numTyVars env_psi A A' →
      TypePrecision numTyVars env_psi B B' →
      CoercPrecision numTyVars env1 env2 c1 A B c2 A' B'

  /-- Right-side Atomic: Handles (any non-sequence c1) ⊑ IsAtomic c2. -/
  | atomic_prec_r {numTyVars env_psi env1 env2 c1 c2 A B A' B'} :
      IsAtomic c2 → 
      (∀ c3 c4, c1 ≠ .seq c3 c4) → 
      TypePrecision numTyVars env_psi A A' →
      TypePrecision numTyVars env_psi B B' →
      CoercPrecision numTyVars env1 env2 c1 A B c2 A' B'

  -- Structural rules (Same constructor on both sides)
  | fn_prec_fn {numTyVars env1 env2 A B C D A' B' C' D' c d c' d'} :
      CoercPrecision numTyVars env1 env2 c C A c' C' A' →
      CoercPrecision numTyVars env1 env2 d B D d' B' D' →
      CoercPrecision numTyVars env1 env2 (.fn c d) (.fn A B) (.fn C D) (.fn c' d') (.fn A' B') (.fn C' D')

  | forall_prec_forall {numTyVars env1 env2 A B A' B' c c'} :
      CoercPrecision (numTyVars + 1) (lift env1) (lift env2) c A B c' A' B' →
      CoercPrecision numTyVars env1 env2 (.forall_ c) (.univ A) (.univ B) (.forall_ c') (.univ A') (.univ B')

  | gen_prec_gen {numTyVars env1 env2 A A' B B' c c'} :
      CoercPrecision (numTyVars + 1) (lift env1) (lift env2) c (liftTy A) B c' (liftTy A') B' →
      CoercPrecision numTyVars env1 env2 (.gen c) A (.univ B) (.gen c') A' (.univ B')

  | inst_prec_inst {numTyVars env1 env2 A B A' B' c c'} :
      CoercPrecision (numTyVars + 1) ((0, Ty.dyn) :: lift env1) ((0, Ty.dyn) :: lift env2) c A (liftTy B) c' A' (liftTy B') →
      CoercPrecision numTyVars env1 env2 (.inst c) (.univ A) B (.inst c') (.univ A') B'

  -- Sequence rules (Decomposition)
  | seq_prec_seq {numTyVars env1 env2 A B C A' B' C' c d c' d'} :
      CoercPrecision numTyVars env1 env2 c A B c' A' B' →
      CoercPrecision numTyVars env1 env2 d B C d' B' C' →
      CoercPrecision numTyVars env1 env2 (.seq c d) A C (.seq c' d') A' C'

  | seq_prec_right {numTyVars env1 env2 A B C A' C' c d c'} :
      CoercPrecision numTyVars env1 env2 c A B c' A' C' →
      CoercPrecision numTyVars env1 env2 d B C c' A' C' →
      CoercPrecision numTyVars env1 env2 (.seq c d) A C c' A' C'

  | left_prec_seq {numTyVars env1 env2 A C A' B' C' c c' d'} :
      CoercPrecision numTyVars env1 env2 c A C c' A' B' →
      CoercPrecision numTyVars env1 env2 c A C d' B' C' →
      CoercPrecision numTyVars env1 env2 c A C (.seq c' d') A' C'

theorem toCoercion_preserves_precision {numTyVars : Nat} {env1 env2 : Env} 
  {A B A' B' : Ty}
  (hEnv : EnvPrecision numTyVars env1 env2)
  (hA : TypePrecision numTyVars env1 A A') 
  (hB : TypePrecision numTyVars env1 B B')
  (cs1 : ConsistentSubtyping numTyVars env1 A B)
  (cs2 : ConsistentSubtyping numTyVars env2 A' B') :
  CoercPrecision numTyVars env1 env2 (toCoercion env1 cs1) A B (toCoercion env2 cs2) A' B' := by
  induction cs1 generalizing A' B' with
  | nat_sub_nat =>
    sorry
  | var_sub_var =>
    sorry
  | dyn_sub_dyn =>
    sorry
  | dyn_sub_var h_lookup =>
    sorry
  | var_sub_dyn h_lookup =>
    sorry
  | dyn_sub_nat =>
    sorry
  | nat_sub_dyn =>
    sorry
  | fn_sub_dyn hC hD ihC ihD =>
    sorry
  | dyn_sub_fn hC hD ihC ihD =>
    sorry
  | fn_sub_fn hC hD ihC ihD =>
    sorry
  | univ_sub_univ h ih =>
    sorry
  | sub_univ h ih =>
    sorry
  | univ_sub h ih =>
    sorry
