/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import VersoManual

import KVACDocs.DocCore
import KVACDocs.DocPreliminaries
import KVACDocs.DocProofSystems
import KVACDocs.DocFramework
import KVACDocs.DocMicroCMZ
import KVACDocs.DocMicroBBS
import KVACDocs.DocConcreteRun

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option doc.verso true
set_option pp.rawOnError true


#doc (Manual) "Keyed-Verification Anonymous Credentials in Lean" =>
%%%
shortTitle := "KVAC in Lean"
%%%

A Lean 4 formalisation of the keyed-verification anonymous credential
(KVAC) framework of Orrù, *Revisiting Keyed-Verification Anonymous
Credentials*, [IACR ePrint 2024/1552](https://eprint.iacr.org/2024/1552)
(cited throughout as *O24*), together with two concrete instantiations:

- *μCMZ* (O24, Section 5) — an improved Chase–Meiklejohn–Zaverucha
  (2014) scheme with O(1) issuance cost, statistical anonymity, and
  security in the algebraic group model under 3-DL.
- *μBBS* (O24, Section 6) — an improved BBDT17 / BBS-MAC scheme with one
  fewer group element per signature, alignment with the IETF BBS draft,
  and security in the algebraic group model under q-DL.

The formalisation is *paper-driven*: the `KVAC/` source tree mirrors the
paper's section structure, and the abstract framework `KVAC/Framework/`
is stated against the paper-level definitions of Section 4 without
committing to any concrete curve, hash function, or deployment.
Concrete bindings — currently a verified Ristretto255 instance from
[curve25519-dalek-lean-verify](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify) —
are isolated under `KVAC/Instances/` and only reached from
`KVAC/Examples/`.

The source code is available on
[GitHub](https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model).
For the formalisation plan, work breakdown, and current status see
`docs/PLAN.md` and `docs/TRACKS.md` in the repository.

# Preface

The paper's structure is bottom-up: an abstract KVAC framework is
defined from an algebraic MAC, and the two concrete schemes are then
proven to realise it. This documentation mirrors that flow chapter by
chapter:

1. *Core* — the algebraic typeclass API (prime-order group, hash, NIZK,
   algebraic MAC) shared by every higher layer.
2. *Preliminaries* — cryptographic background (Section 3 of O24):
   hardness assumptions, ZK argument syntax, anonymous-token syntax.
3. *Proof systems* — Σ-protocol meta-theory and the straight-line
   extraction infrastructure (Section 9 of O24).
4. *Framework* — the abstract KVAC scheme: syntax, correctness,
   anonymity, extractability (Section 4 of O24).
5. *μCMZ* — first concrete scheme plus its security proofs (Section 5).
6. *μBBS* — second concrete scheme plus its security proofs (Section 6).
7. *Concrete run* — a μCMZ end-to-end example over Ristretto255.

{include 1 KVACDocs.DocCore}
{include 1 KVACDocs.DocPreliminaries}
{include 1 KVACDocs.DocProofSystems}
{include 1 KVACDocs.DocFramework}
{include 1 KVACDocs.DocMicroCMZ}
{include 1 KVACDocs.DocMicroBBS}
{include 1 KVACDocs.DocConcreteRun}
