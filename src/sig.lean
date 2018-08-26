import category_theory.category

inductive bwd (α : Type) : Type
| emp {} : bwd
| snoc : bwd → α → bwd

notation `ε` := @bwd.emp _
infixl `≪`:5 := @bwd.snoc _
notation `⟪` l:(foldl `, ` (h t, (t ≪ h)) ε `⟫`) := l

@[simp]
def append {α} : bwd α → list α → bwd α
| xs [] := xs
| xs (y :: ys) := append (xs ≪ y) ys

infixl `⋉`:3 := append



def fam (α : Type) := α → Type



/-- Thinnings -/
inductive thn {α} : bwd α → bwd α → Type
| emp {} : thn ⟪⟫ ⟪⟫
| cong {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) (Δ ≪ τ)
| drop {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) Δ

infixr `⇾`:30 := @thn _
infixl `≤` := @thn _

def idn {α} : Π (Γ : bwd α), Γ ⇾ Γ
| bwd.emp := thn.emp
| (bwd.snoc Γ _) := thn.cong (idn Γ)

def seq {α} : Π {Γ Δ Ξ : bwd α}, Γ ⇾ Δ → Δ ⇾ Ξ → Γ ⇾ Ξ
| _ _ _ thn.emp thn.emp := thn.emp
| _ _ _ (thn.cong δ) (thn.cong ξ) := thn.cong (seq δ ξ)
| _ _ _ (thn.cong δ) (thn.drop ξ) := thn.drop (seq δ ξ)
| _ _ _ (thn.drop δ) ξ := thn.drop (seq δ ξ)

theorem seq_left_idn {α} : Π {Γ Δ : bwd α} (γ : Δ ⇾ Γ), seq (idn _) γ = γ
| _ _ thn.emp := by refl
| _ _ (thn.cong ξ) :=
  begin
    unfold idn seq,
    rewrite (seq_left_idn ξ)
  end
| _ _ (thn.drop ξ) :=
  begin
    unfold idn seq,
    rewrite (seq_left_idn ξ)
  end



inductive arity (α : Type) : Type
| mk : list arity → α → arity

def sig (α : Type) := fam (arity α)
infixl `▶`:3 := arity.mk



/-- the clone (type of terms) and type of substitutions -/
mutual inductive cn, sb {α} (𝔖 : sig α)
with cn : bwd (arity α) → α → Type
| opr {Γ Δ τ} : 𝔖 (Δ ▶ τ) → sb Γ Δ → cn Γ τ
| var {Γ Δ τ} : Γ ⇾ ⟪ Δ ▶ τ ⟫ → sb Γ Δ → cn Γ τ
with sb : bwd (arity α) → list (arity α) → Type
| nil {Γ} : sb Γ []
| cons {Γ Ξ Δ τ} : cn (Γ ⋉ Δ) τ → sb Γ Ξ → sb Γ ((Δ ▶ τ) :: Ξ)


namespace lambda_calculus
  inductive sort : Type
  | chk
  | syn

  open sort

  inductive LAM : arity sort → Type
  | lam : LAM ([[[] ▶ syn] ▶ chk] ▶ chk)
  | app : LAM ([[] ▶ syn, [] ▶ chk] ▶ syn)
  | up : LAM ([[] ▶ syn] ▶ chk)

  infix `∙`:5 := cn.opr

  notation `⦃` l:(foldr `, ` (h t, (sb.cons h t)) (sb.nil _) `⦄`) := l

  notation `ƛ` t := LAM.lam ∙ ⦃ t ⦄

  notation ξ `#` γ := cn.var ξ γ
  notation `⇑` t := LAM.up ∙ ⦃ t ⦄
  notation `x₀` := thn.cong thn.emp

  def tm (Γ : bwd (arity sort)) := cn LAM Γ chk


  -- identity function
  def foo : _ :=
    ƛ ⇑ (x₀ # ⦃⦄)

end lambda_calculus
