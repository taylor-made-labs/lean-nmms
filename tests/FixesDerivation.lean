/- Fix 2 kernel examples. API and closure semantics: FIXES-CONTRACT.md. -/
import LeanNmms.Derivation

open NMMS

namespace FixesDerivationTests

def a : Formula String := .atom "amber_seed"
def b : Formula String := .atom "amber_mid"
def c : Formula String := .atom "amber_ready"
def z : Formula String := .atom "invented_permission"

def base : List (Entry String) := [
  { ant := ["amber_seed"], con := ["amber_mid"], rob := .exact },
  { ant := ["amber_mid"], con := ["amber_ready"], rob := .exact },
  { ant := ["invented_permission"], con := ["amber_ready"], rob := .exact }]

def first : DerivationStep String :=
  { premises := [a], conclusion := b, cert := .ax }
def second : DerivationStep String :=
  { premises := [b], conclusion := c, cert := .ax }
def injected : DerivationStep String :=
  { premises := [z], conclusion := c, cert := .ax }

-- Genuine transitive material closure, despite the base having EXACT entries.
example : checkDerivation base [a] [first, second] c = true := by decide
example : checkDerivation base [a] [] a = true := by decide
example : checkDerivation base [a, a] [first, second] c = true := by decide
example : checkDerivation base [] [] a = false := by decide

-- Every local sequent can pass while the chain is forged.
example : check (baseRel base) injected.cert injected.premises [c] = true := by decide
example : checkDerivation base [a] [injected] c = false := by decide
example : checkDerivation base [a] [second, first] c = false := by decide
example : checkDerivation base [a] [first] c = false := by decide
example : checkDerivation base [a] [first, second] z = false := by decide

-- No circular or self support. (`c ⇒ c` is not even an NMMS sequent over this
-- base: NMMS adds no Containment, and the base has no `c |~ c`.)
example : checkDerivation base [a]
    [{ premises := [c], conclusion := c, cert := .ax }] c = false := by decide
example : checkDerivation base []
    [{ premises := [z], conclusion := z, cert := .ax }] z = false := by decide

-- Checking availability alone is insufficient: this local proof is invalid.
example : checkDerivation base [a]
    [{ premises := [a], conclusion := c, cert := .ax }] c = false := by decide

-- Check a complex proof tree as well as atomic axiom leaves. The leaf
-- `amber_seed, amber_mid ⇒ amber_seed` must be in the base: Containment is not
-- added, so over the empty base the same step is refused.
def pair : Formula String := .conj a b
def unpack : DerivationStep String := {
  premises := [pair], conclusion := a,
  cert := .node true pair false .ax .ax .ax }
def pairBase : List (Entry String) := [
  { ant := ["amber_seed", "amber_mid"], con := ["amber_seed"], rob := .exact }]
example : checkDerivation pairBase [pair] [unpack] a = true := by decide
example : checkDerivation [] [pair] [unpack] a = false := by decide
example : checkDerivation pairBase [a] [unpack] a = false := by decide
example : check (baseRel ([] : List (Entry String))) .ax [a] [a] = false := by decide

-- This pins the soundness theorem's type, not merely the existence of a name.
example (steps : List (DerivationStep String)) (claim : Formula String)
    (accepted : checkDerivation base [a] steps claim = true) :
    Closure base [a] claim := checkDerivation_sound accepted

end FixesDerivationTests
