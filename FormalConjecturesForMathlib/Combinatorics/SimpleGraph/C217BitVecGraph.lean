/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.C217BooleanGraph
import Mathlib.Data.BitVec.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A surjective BitVec encoding of finite simple graphs

The LRAT certificates use one fixed-width bitvector as their only SAT input.
`finProdFinEquiv` identifies matrix positions with bit positions, and
`bitVecOfFn` proves that every Boolean matrix—and therefore every simple graph—is
represented exactly.
-/

namespace SimpleGraph.C217BitVecGraph

open Classical
open SimpleGraph
open SimpleGraph.C217BooleanGraph

/-- Build a bitvector from its least-significant-bit-indexed Boolean function. -/
def bitVecOfFn : {n : ℕ} → (Fin n → Bool) → BitVec n
  | 0, _ => .nil
  | n + 1, f =>
      BitVec.cons (f ⟨n, by omega⟩)
        (bitVecOfFn fun i : Fin n => f i.castSucc)

/-- Reading `bitVecOfFn f` returns `f`. -/
theorem getLsb_bitVecOfFn : ∀ {n : ℕ} (f : Fin n → Bool) (i : Fin n),
    (bitVecOfFn f).getLsb i = f i
  | 0, _, i => Fin.elim0 i
  | n + 1, f, i => by
      rw [BitVec.getLsb_eq_getElem]
      simp only [bitVecOfFn, BitVec.getElem_cons]
      split
      · rename_i h
        have hi : i = ⟨n, by omega⟩ := Fin.ext h
        subst i
        rfl
      · rename_i h
        have hi : i.val < n := by omega
        have ih := getLsb_bitVecOfFn
          (fun j : Fin n => f j.castSucc) ⟨i.val, hi⟩
        simpa [BitVec.getLsb_eq_getElem] using ih

/-- Read a row-major Boolean matrix entry from a bitvector. -/
def matrixBit {n : ℕ} (bits : BitVec (n * n)) (i j : Fin n) : Bool :=
  bits.getLsb (finProdFinEquiv (i, j))

/-- Canonical simple graph represented by a matrix bitvector. -/
def graphOfBitVec {n : ℕ} (bits : BitVec (n * n)) : SimpleGraph (Fin n) :=
  graphOfMatrix (matrixBit bits)

/-- Encode a graph's Boolean adjacency matrix as a bitvector. -/
def bitVecOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : BitVec (n * n) :=
  bitVecOfFn fun k =>
    let ij := finProdFinEquiv.symm k
    decide (G.Adj ij.1 ij.2)

@[simp] theorem matrixBit_bitVecOfGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    matrixBit (bitVecOfGraph G) i j = decide (G.Adj i j) := by
  simp [matrixBit, bitVecOfGraph, getLsb_bitVecOfFn]

/-- Every finite simple graph is recovered exactly by the bitvector encoding. -/
theorem graphOfBitVec_bitVecOfGraph_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    graphOfBitVec (bitVecOfGraph G) = G := by
  unfold graphOfBitVec
  rw [show matrixBit (bitVecOfGraph G) = matrixOfGraph G by
    funext i j
    exact matrixBit_bitVecOfGraph G i j]
  exact graphOfMatrix_matrixOfGraph_eq G

#print axioms SimpleGraph.C217BitVecGraph.getLsb_bitVecOfFn
#print axioms SimpleGraph.C217BitVecGraph.graphOfBitVec_bitVecOfGraph_eq

end SimpleGraph.C217BitVecGraph
