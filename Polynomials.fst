module Polynomials

/// In this module, we will construct polynomials over arbitrary commutative rings.
/// For short, I call a polynomial a poly, plural polys.
 
open AlgebraTypes
   
open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties

/// Polys are defined as a refinement of seq c, where c is the type for which
/// the coefficient ring is defined.

/// Basic definitions for the noncompact poly type, construction functions and emptiness checks.
open Polynomials.Definition

/// Poly equality definition and aux lemmas. Trailing zeros are processed correctly.
open Polynomials.Equivalence
/// Poly compact procedure, i.e. removal of trailing zeros.
/// Lemmas that it does not affect poly equality.
open Polynomials.Compact
/// Poly addition and negation.
open Polynomials.Addition
open Polynomials.Monomial
open Polynomials.Multiplication

/// Poly multiplication is not finished yet.
/// Completed steps:
/// * Definition
/// * Commutativity 
/// Note: poly multiplication is defined as the sum of (ai*bj)x^{i+j}. Matrix is flattened,
/// then proven to be a permutation of the flattened matrix (bj*ai)x^{j+i} since the
/// coefficient ring is commutative.
///
/// To be done:
/// * Ring structure construction 
/// 
/// Note: multiplication inverses only exist for polys if the constant coefficient is invertible
/// and all the other nonzero coefficients are nilpotent. It's a theorem in ring theory. 

open FStar.Math.Lemmas
 
