# Endless games of War, losing card first (OEIS A400868): a complete, formally verified proof of Spivey's construction

This repository contains a complete written proof, machine-checked in Lean 4, of the **known half** of the conjecture recorded in OEIS [A400868](https://oeis.org/A400868).

**Prior work.** This half is not new. M. Z. Spivey, *Cycles in War*, Integers 10 (2010), p. 762, already observed that when the losing card goes first, a version of his doubling construction (his Theorem 3) gives cycles for every n that is not a power of 2. He states this as a remark, without a separate proof for this rule. Our contribution is a self-contained proof for this rule (including a balanced deal), its **formal verification in Lean 4**, a structure theorem for odd n, and computational observations on the open direction.

**The game.** Two players hold the cards 1, …, n. At each turn both reveal their top card. The higher card wins, and the winner puts **the losing card, then the winning card**, at the bottom of their pile. A player with no cards loses.

**The conjecture** (D. Okwor, OEIS A400868): some deal never ends **if and only if n is not a power of 2**.

## Results

> **Theorem 1 (announced by Spivey, 2010; complete proof here, verified in Lean 4).** For every n ≥ 1 that is not a power of 2, there is a deal of ⌈n/2⌉ and ⌊n/2⌋ of the cards 1, …, n whose game never ends. Hence A400868(n) > 0.

> **Theorem 2 (written proof).** Let n be odd. In every cycle, the card that won its previous turn always beats the card that lost its previous turn. Hence every card keeps its role forever, and the players win alternately.

**Still open:** the converse, that no game of 2^k cards is endless. The paper records computational observations on it, including two strategies that fail.

**Idea of the proof of Theorem 1.** Let s(i) be the number of 1s in the binary expansion of i. A block B_k(v) is the sequence of 2^k labels v − k + s(i), for 0 ≤ i < 2^k. Over 2^k turns, a block B_k(x) facing a block B_k(x+1) behaves exactly like one card facing another: the second player wins every turn and puts back B_{k+1}(x+1) = B_k(x) B_k(x+1). Write n = m·2^k with m ≥ 3 odd. The 2-turn loop of m cards ((1,2)^((m−1)/2) | (2)) then blows up to an endless game of n cards. A rewinding lemma turns it into a balanced deal.

Example (n = 10): the deal `(8, 5, 9, 1, 3 | 4, 2, 6, 7, 10)` never ends.

## Contents

| File | Description |
|---|---|
| `A400868_paper.pdf` | The paper (English): proofs, references, credits |
| `A400868_paper.tex` | LaTeX source of the paper |
| `A400868_easy_direction.lean` | Complete Lean 4 formalization of Theorem 1 (423 lines) |
| `checks/construct_and_replay.py` | Checks the construction and the balanced deals for all n ≤ 200 |
| `checks/odd_and_powers.py` | Exhaustive checks: no cycle for n = 2, 4, 8; Theorem 2 for odd n ≤ 9 |

## The formal statement

```lean
theorem easy_direction (n : ℕ) (hn : 0 < n) (hnot : ¬∃ k : ℕ, n = 2^k) :
    ∃ s : State ℕ, (s.1 ++ s.2).Perm (List.range' 1 n) ∧
      s.1.length = (n+1)/2 ∧ s.2.length = n/2 ∧ NeverEnds s
```

The game is defined directly on lists: in `step`, the winner appends the smaller card, then the larger card. `NeverEnds s` means that both piles are nonempty after any number of turns.

## How to check

Requirements: Lean `4.36.0-rc2` and Mathlib commit `9d581dfff2e41de989072ea63abf3daf69311520`.

```bash
lake env lean A400868_easy_direction.lean
```

Expected result: no errors and no `sorry`, and `#print axioms easy_direction` reports only `[propext, Classical.choice, Quot.sound]`.

SHA-256 of `A400868_easy_direction.lean`:
`115b104bf10ee992bbefa75ffcae1e89b70db4b75ed3037243fae3e60a198e2c`

Independent checks (Python 3, no dependencies):

```bash
python3 checks/construct_and_replay.py 200
python3 checks/odd_and_powers.py
```

## Credits and use of AI

This work was produced under the pseudonym A-guy-with-AI, in collaboration with AI systems:

- **Claude (Anthropic):** choice of the problem, the block construction (a variant of Spivey's doubling), the proofs of Theorems 1 and 2, an independent recompilation of the Lean file.
- **ChatGPT (OpenAI):** review of the proofs, the complete Lean formalization, independent enumerations and large-scale computations.

The sequence, the conjecture and the data are due to **D. Okwor** ([Zenodo](https://doi.org/10.5281/zenodo.22957686), [programs and data](https://github.com/OrygnsCode/endless-games-of-war)). The constructive direction for this rule is due to M. Z. Spivey, *Cycles in War*, Integers 10 (2010), p. 762.

## License

MIT, see `LICENSE`.
