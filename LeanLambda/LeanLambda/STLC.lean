-- Extrinsically typed STLC with de Bruijn indices
namespace STLC

-------------------------------------------------------------------------------
-- 1. SYNTAX & TYPES
-------------------------------------------------------------------------------

inductive Ty where
  | nat : Ty
  | fn  : Ty → Ty → Ty
  deriving BEq

infixr:70 " ⇒ " => Ty.fn

inductive Raw where
  | var  : Nat → Raw
  | lam  : Ty → Raw → Raw
  | app  : Raw → Raw → Raw
  | zero : Raw
  | suc  : Raw → Raw
  | case : Raw → Raw → Raw → Raw
  | mu   : Ty → Raw → Raw

-------------------------------------------------------------------------------
-- 2. RENAMING & PARALLEL SUBSTITUTION
-------------------------------------------------------------------------------

def ext (ρ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Nat → Nat) : Raw → Raw
  | .var i      => .var (ρ i)
  | .lam A N    => .lam A (rename (ext ρ) N)
  | .app L M    => .app (rename ρ L) (rename ρ M)
  | .zero       => .zero
  | .suc M      => .suc (rename ρ M)
  | .case L M N => .case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  | .mu A N     => .mu A (rename (ext ρ) N)

def exts (σ : Nat → Raw) : Nat → Raw
  | 0     => .var 0
  | i + 1 => rename (Nat.succ) (σ i)

def subst (σ : Nat → Raw) : Raw → Raw
  | .var i      => σ i
  | .lam A N    => .lam A (subst (exts σ) N)
  | .app L M    => .app (subst σ L) (subst σ M)
  | .zero       => .zero
  | .suc M      => .suc (subst σ M)
  | .case L M N => .case (subst σ L) (subst σ M) (subst (exts σ) N)
  | .mu A N     => .mu A (subst (exts σ) N)

def single_subst (N : Raw) (M : Raw) : Raw :=
  let σ : Nat → Raw
    | 0     => M
    | i + 1 => .var i
  subst σ N

-------------------------------------------------------------------------------
-- 3. TYPING RELATION (Defined in Type for constructivity)
-------------------------------------------------------------------------------

abbrev Context := List Ty

inductive HasTypeVar : Context → Nat → Ty → Type where
  | Z : ∀ {Γ A}, HasTypeVar (A :: Γ) 0 A
  | S : ∀ {Γ A B i}, HasTypeVar Γ i A → HasTypeVar (B :: Γ) (i + 1) A

inductive HasType : Context → Raw → Ty → Type where
  | t_var : ∀ {Γ i A},
      HasTypeVar Γ i A → HasType Γ (.var i) A
  | t_lam : ∀ {Γ A B N},
      HasType (A :: Γ) N B → HasType Γ (.lam A N) (A ⇒ B)
  | t_app : ∀ {Γ A B L M},
      HasType Γ L (A ⇒ B) → HasType Γ M A → HasType Γ (.app L M) B
  | t_zero : ∀ {Γ},
      HasType Γ .zero .nat
  | t_suc : ∀ {Γ M},
      HasType Γ M .nat → HasType Γ (.suc M) .nat
  | t_case : ∀ {Γ A L M N},
      HasType Γ L .nat →
      HasType Γ M A →
      HasType (.nat :: Γ) N A →
      HasType Γ (.case L M N) A
  | t_mu : ∀ {Γ A N},
      HasType (A :: Γ) N A → HasType Γ (.mu A N) A

-------------------------------------------------------------------------------
-- 4. VALUES & REDUCTION
-------------------------------------------------------------------------------

inductive Value : Raw → Type where
  | v_lam  : ∀ {A N}, Value (.lam A N)
  | v_zero : Value .zero
  | v_suc  : ∀ {V}, Value V → Value (.suc V)

inductive Step : Raw → Raw → Type where
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {V M M'}, Value V → Step M M' → Step (.app V M) (.app V M')
  | β_lam   : ∀ {A N W}, Value W → Step (.app (.lam A N) W) (single_subst N W)
  | xi_suc  : ∀ {M M'}, Step M M' → Step (.suc M) (.suc M')
  | xi_case : ∀ {L L' M N}, Step L L' → Step (.case L M N) (.case L' M N)
  | β_zero  : ∀ {M N}, Step (.case .zero M N) M
  | β_suc   : ∀ {V M N}, Value V → Step (.case (.suc V) M N) (single_subst N V)
  | β_mu    : ∀ {A N}, Step (.mu A N) (single_subst N (.mu A N))

infix:20 " —→ " => Step

-------------------------------------------------------------------------------
-- 5. STRUCTURAL LEMMAS
-------------------------------------------------------------------------------

def typing_rename {Γ Δ : Context} {ρ : Nat → Nat} {M : Raw} {A : Ty}
  (hρ : ∀ {i B}, HasTypeVar Γ i B → HasTypeVar Δ (ρ i) B)
  (hM : HasType Γ M A) : HasType Δ (rename ρ M) A :=
  match hM with
  | .t_var hV => .t_var (hρ hV)
  | .t_lam (A := A) (B := B) hN =>
      let hρ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasTypeVar (A :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_lam (typing_rename hρ' hN)
  | .t_app hL hM => .t_app (typing_rename hρ hL) (typing_rename hρ hM)
  | .t_zero => .t_zero
  | .t_suc hM => .t_suc (typing_rename hρ hM)
  | .t_case (A := A) hL hM hN =>
      let hρ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasTypeVar (Ty.nat :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hρ' hN)
  | .t_mu (A := A) hN =>
      let hρ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasTypeVar (A :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_mu (typing_rename hρ' hN)

def typing_subst {Γ Δ : Context} {σ : Nat → Raw} {M : Raw} {A : Ty}
  (hσ : ∀ {i B}, HasTypeVar Γ i B → HasType Δ (σ i) B)
  (hM : HasType Γ M A) : HasType Δ (subst σ M) A :=
  match hM with
  | .t_var hV => hσ hV
  | .t_lam (A := A) (B := B) hN =>
      let hσ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasType (A :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              -- We use an explicit lambda for the renaming map
              typing_rename (Δ := A :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_lam (typing_subst hσ' hN)
  | .t_app hL hR => .t_app (typing_subst hσ hL) (typing_subst hσ hR)
  | .t_zero => .t_zero
  | .t_suc hK => .t_suc (typing_subst hσ hK)
  | .t_case (A := A) hL hM hN =>
      let hσ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasType (Ty.nat :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              typing_rename (Δ := Ty.nat :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_case (typing_subst hσ hL) (typing_subst hσ hM) (typing_subst hσ' hN)
  | .t_mu (A := A) hN =>
      let hσ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasType (A :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              typing_rename (Δ := A :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_mu (typing_subst hσ' hN)

def typing_single_subst {Γ : Context} {A B : Ty} {N M : Raw}
  (hN : HasType (B :: Γ) N A) (hM : HasType Γ M B) :
  HasType Γ (single_subst N M) A := by
  -- Define the mapping: 0 goes to M, and j+1 shifts down to j
  let σ := fun (i : Nat) => match i with | 0 => M | j+1 => .var j

  -- Apply the substitution lemma
  refine typing_subst (Δ := Γ) (σ := σ) ?_ hN

  -- Prove the substitution is well-typed for all variables
  intro i C hVar
  cases hVar with
  | Z =>
    -- Case i = 0: σ(0) = M. We know Γ ⊢ M : B from hM.
    exact hM
  | S hVar' =>
    -- Case i = j+1: σ(j+1) = var j.
    -- Since the context was (B :: Γ), index j+1 had type C.
    -- Therefore, in Γ, index j has type C.
    exact .t_var hVar'

-------------------------------------------------------------------------------
-- 6. PROGRESS & PRESERVATION
-------------------------------------------------------------------------------

def preservation {M N : Raw} {A : Ty}
  (hT : HasType [] M A) (hS : M —→ N) : HasType [] N A :=
  match hS with
  | .β_lam hV =>
      match hT with
      | .t_app (.t_lam hN) hM => typing_single_subst hN hM
  | .β_zero =>
      match hT with
      | .t_case _ hM _ => hM
  | .β_suc hV =>
      match hT with
      | .t_case (.t_suc hL) _ hN => typing_single_subst hN hL
  | .β_mu (A := ATy) (N := Body) =>
      match hT with
      | .t_mu hN => typing_single_subst hN (.t_mu hN)
  | .xi_app1 s =>
      match hT with
      | .t_app hL hM => .t_app (preservation hL s) hM
  | .xi_app2 v s =>
      match hT with
      | .t_app hL hM => .t_app hL (preservation hM s)
  | .xi_suc s =>
      match hT with
      | .t_suc hM => .t_suc (preservation hM s)
  | .xi_case s =>
      match hT with
      | .t_case hL hM hN => .t_case (preservation hL s) hM hN

inductive ProgressResult (M : Raw) where
  | step : ∀ {N}, (M —→ N) → ProgressResult M
  | done : Value M → ProgressResult M

def progress {Γ : Context} {M : Raw} {A : Ty} (h : HasType Γ M A) :
  Γ = [] → ProgressResult M := fun hEmpty =>
  match Γ, M, A, h with
  | _, .var i, _, .t_var hV => by subst hEmpty; nomatch hV
  | _, .lam A N, _, .t_lam hN => .done .v_lam
  | _, .app L M, B, .t_app hL hM =>
      match progress hL hEmpty, progress hM hEmpty with
      | .step s, _ => .step (.xi_app1 s)
      | .done vL, .step s => .step (.xi_app2 vL s)
      | .done vL, .done vM => match L, vL with | .lam _ _, .v_lam => .step (.β_lam vM)
  | _, .zero, _, .t_zero => .done .v_zero
  | _, .suc M, _, .t_suc hM =>
      match progress hM hEmpty with | .step s => .step (.xi_suc s) | .done v => .done (.v_suc v)
  | _, .case L M N, A, .t_case hL hM hN =>
      match progress hL hEmpty with
      | .step s => .step (.xi_case s)
      | .done vL => match L, vL with
          | .zero, .v_zero => .step .β_zero
          | .suc _, .v_suc v => .step (.β_suc v)
  | _, .mu A N, _, .t_mu hN => .step .β_mu

def progress_top {M : Raw} {A : Ty} (h : HasType [] M A) : ProgressResult M :=
  progress h rfl

-- Ported from Agda: lecture-notes-Substitution

-------------------------------------------------------------------------------
-- 1. SIGMA-CALCULUS DEFINITIONS
-------------------------------------------------------------------------------

/-- Substitution sequencing (σ ⨟ τ): Applying τ to the result of σ -/
def seq (σ₁ : Nat → Raw) (σ₂ : Nat → Raw) : Nat → Raw :=
  fun i => subst σ₂ (σ₁ i)

infixr:50 " ⨟ " => seq

/-- Substitution for single term at index 1: N 〔 M 〕 -/
def subst_one_at_one (N : Raw) (M : Raw) : Raw :=
  subst (exts (fun i => match i with | 0 => M | j+1 => .var j)) N

-------------------------------------------------------------------------------
-- 2. CORE SUBSTITUTION THEOREMS
-------------------------------------------------------------------------------

/-- Lemma: Composition of extensions is the extension of the composition.
    Corresponds to `ext-equiv` and `Z-shiftʳ` in the Agda source[cite: 1]. -/
theorem ext_comp (ρ₁ ρ₂ : Nat → Nat) :
  (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ n => rfl

/-- rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M -/
theorem rename_rename_commute (ρ₁ ρ₂ : Nat → Nat) (M : Raw) :
  rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M := by
  induction M generalizing ρ₁ ρ₂ with
  | var i => 
    -- Variables are trivially renamed[cite: 8].
    rfl
  | lam A N ih =>
    -- For lambdas, we apply the inductive hypothesis to the body N.
    -- We use ext_comp to rewrite the composition of extended environments.
    simp only [rename]
    rw [ih (ext ρ₁) (ext ρ₂), ext_comp]
  | app L R ihL ihR =>
    -- Applications distribute the renaming to both sides[cite: 10].
    simp only [rename]
    rw [ihL, ihR]
  | zero => 
    -- Zero is a constant, so it remains unchanged[cite: 11].
    rfl
  | suc M ih =>
    -- Successor simply applies to its inner term[cite: 12].
    simp only [rename]
    rw [ih]
  | case L M N ihL ihM ihN =>
    -- Case statements distribute to all three branches[cite: 13].
    -- The N branch binds a variable, so we use ext_comp again.
    simp only [rename]
    rw [ihL, ihM, ihN (ext ρ₁) (ext ρ₂), ext_comp]
  | mu A N ih =>
    -- Mu binds a variable, handled exactly like lam[cite: 14].
    simp only [rename]
    rw [ih (ext ρ₁) (ext ρ₂), ext_comp]

/-- Helper lemma: composing `ext` and `exts` is equivalent to extending the composition. -/
theorem exts_ext_comp (ρ : Nat → Nat) (τ : Nat → Raw) :
  (fun i => exts τ (ext ρ i)) = exts (fun i => τ (ρ i)) := by
  funext i
  cases i with
  | zero => 
    -- exts τ (ext ρ 0) = exts τ 0 = .var 0
    -- exts (fun i => τ (ρ i)) 0 = .var 0
    rfl
  | succ n => 
    -- exts τ (ext ρ (n+1)) = exts τ (ρ n + 1) = rename Nat.succ (τ (ρ n))
    -- exts (fun i => τ (ρ i)) (n+1) = rename Nat.succ (τ (ρ n))
    rfl

/-- Renaming followed by substitution is equivalent to a composed substitution. -/
theorem rename_subst_commute (ρ : Nat → Nat) (τ : Nat → Raw) (M : Raw) :
  subst τ (rename ρ M) = subst (fun i => τ (ρ i)) M := by
  induction M generalizing ρ τ with
  | var i => 
    -- Variables evaluate directly to τ (ρ i) on both sides
    rfl
  | lam A N ih =>
    -- Under a lambda, we use the inductive hypothesis and our helper lemma
    simp only [rename, subst]
    rw [ih (ext ρ) (exts τ), exts_ext_comp]
  | app L R ihL ihR =>
    -- Application distributes to both subterms
    simp only [rename, subst]
    rw [ihL, ihR]
  | zero => 
    -- Constants remain unchanged
    rfl
  | suc M ih =>
    simp only [rename, subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    -- Case statements distribute; the N branch binds a variable
    simp only [rename, subst]
    rw [ihL, ihM, ihN (ext ρ) (exts τ), exts_ext_comp]
  | mu A N ih =>
    -- Mu binds a variable, handled exactly like lam
    simp only [rename, subst]
    rw [ih (ext ρ) (exts τ), exts_ext_comp]

/-- Helper 1: Commuting `ext` (renaming extension) and `exts` (substitution extension). -/
theorem ext_exts_comp (ρ : Nat → Nat) (τ : Nat → Raw) :
  (fun i => rename (ext ρ) (exts τ i)) = exts (fun i => rename ρ (τ i)) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    -- Focus on the `succ` case and use `rename_rename_commute` twice
    change rename (ext ρ) (rename Nat.succ (τ j)) = rename Nat.succ (rename ρ (τ j))
    rw [rename_rename_commute, rename_rename_commute]
    rfl

/-- Helper 2: Renaming a substitution is equivalent to substituting with renamed terms. -/
theorem rename_subst (ρ : Nat → Nat) (τ : Nat → Raw) (M : Raw) :
  rename ρ (subst τ M) = subst (fun i => rename ρ (τ i)) M := by
  induction M generalizing ρ τ with
  | var i => rfl
  | lam A N ih =>
    simp only [rename, subst]
    rw [ih, ext_exts_comp]
  | app L R ihL ihR =>
    simp only [rename, subst]
    rw [ihL, ihR]
  | zero => rfl
  | suc M ih =>
    simp only [rename, subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [rename, subst]
    rw [ihL, ihM, ihN, ext_exts_comp]
  | mu A N ih =>
    simp only [rename, subst]
    rw [ih, ext_exts_comp]

/-- Helper 3: Extending a composed substitution is the composition of extended substitutions. -/
theorem exts_seq (σ τ : Nat → Raw) :
  (exts σ ⨟ exts τ) = exts (σ ⨟ τ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j =>
    -- Simplify to expose the inner `rename` and `subst` applications
    dsimp [seq, exts]
    -- Use the previously proven commutation lemmas on both sides
    rw [rename_subst_commute, rename_subst]
    rfl

/-- Main Theorem: Double substitution is equivalent to substituting a composed mapping. -/
theorem sub_sub (σ τ : Nat → Raw) (M : Raw) :
  subst τ (subst σ M) = subst (σ ⨟ τ) M := by
  induction M generalizing σ τ with
  | var i => 
    rfl
  | lam A N ih =>
    simp only [subst]
    rw [ih, exts_seq]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]
  | zero => 
    rfl
  | suc M ih =>
    simp only [subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [subst]
    rw [ihL, ihM, ihN, exts_seq]
  | mu A N ih =>
    simp only [subst]
    rw [ih, exts_seq]

/-- Helper: Substitution with the variable constructor is the identity. -/
theorem subst_id (M : Raw) : subst Raw.var M = M := by
  induction M with
  | var i => rfl
  | lam A N ih =>
    simp only [subst]
    have h_exts : exts Raw.var = Raw.var := by
      funext i; cases i <;> rfl
    rw [h_exts, ih]
  | app L R ihL ihR =>
    simp only [subst]
    rw [ihL, ihR]
  | zero => rfl
  | suc M ih =>
    simp only [subst]
    rw [ih]
  | case L M N ihL ihM ihN =>
    simp only [subst]
    have h_exts : exts Raw.var = Raw.var := by
      funext i; cases i <;> rfl
    rw [h_exts, ihL, ihM, ihN]
  | mu A N ih =>
    simp only [subst]
    have h_exts : exts Raw.var = Raw.var := by
      funext i; cases i <;> rfl
    rw [h_exts, ih]

/-- The main substitution lemma: M[N][L] = M[L][N[L]] -/
theorem substitution {M N L : Raw} :
  single_subst (single_subst M N) L =
    single_subst (subst_one_at_one M L) (single_subst N L) := by
  -- Unfold the custom substitution definitions into raw `subst` applications
  dsimp only [single_subst, subst_one_at_one]
  
  -- Apply our `sub_sub` lemma to both sides to fuse the double substitutions
  rw [sub_sub, sub_sub]
  
  -- We prove the composed substitution environments are pointwise identical.
  -- Using congrArg forces Lean to ONLY strip the outer `subst ... M`,
  -- avoiding `congr`'s aggressive and destructive unifications.
  apply congrArg (fun (σ : Nat → Raw) => subst σ M)
  funext i
  cases i with
  | zero =>
    -- Case i = 0: Both evaluate definitionally to `single_subst N L`
    rfl
  | succ j =>
    cases j with
    | zero =>
      -- Case i = 1: 
      -- The LHS evaluates cleanly to `L`.
      -- The RHS evaluates to `subst τ (rename Nat.succ L)`.
      -- We use `change` to bypass brittle unfolding tactics and let the kernel verify it.
      change L = subst (fun x => match x with | 0 => single_subst N L | y+1 => Raw.var y) (rename Nat.succ L)
      
      -- Flip the equation to match the commutation lemma
      symm
      
      -- Commute the renaming and substitution on the RHS
      rw [rename_subst_commute]
      
      -- After commutation, the mapped function evaluates exactly to `Raw.var`.
      change subst Raw.var L = L
      
      -- Apply our identity helper lemma backwards
      exact subst_id L
    | succ k =>
      -- Case i = k + 2: Both mappings shift and evaluate nicely to `.var k`
      rfl

/-- Substituting into an extended substitution is equivalent to a single mapping. -/
theorem exts_sub_cons {σ : Nat → Raw} {N : Raw} {V : Raw} :
  single_subst (subst (exts σ) N) V =
    subst (fun i => match i with | 0 => V | j+1 => σ j) N := by
  -- Unfold the definition of single_subst
  dsimp only [single_subst]
  
  -- Fuse the double substitution into a single composed substitution
  rw [sub_sub]
  
  -- Apply congrArg to isolate the substitution environments
  apply congrArg (fun (env : Nat → Raw) => subst env N)
  funext i
  cases i with
  | zero => 
    -- Case i = 0: Both evaluate to `V`
    rfl
  | succ j =>
    -- Case i = j + 1:
    -- The LHS evaluates to `subst τ (rename Nat.succ (σ j))`
    dsimp only [seq, exts]
    
    -- Commute the rename and subst operations
    rw [rename_subst_commute]
    
    -- The composed mapping function strictly evaluates to `Raw.var`
    change subst Raw.var (σ j) = σ j
    
    -- Close the goal with our identity lemma
    exact subst_id (σ j)

end STLC
