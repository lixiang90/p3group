# P3Group

Formalization of the **classification of groups of order \(p^3\)** in Lean 4,
using [mathlib4](https://github.com/leanprover-community/mathlib4).

## Main result

Every finite group of order \(p^3\) (where \(p\) is prime) is isomorphic to one
of five groups.  Up to isomorphism they are:

**p odd**

| Group | Structure |
|---|---|
| Cyclic | \(\mathbb{Z}/p^3\mathbb{Z}\) |
| Abelian | \(\mathbb{Z}/p^2\mathbb{Z} \times \mathbb{Z}/p\mathbb{Z}\) |
| Elementary abelian | \((\mathbb{Z}/p\mathbb{Z})^3\) |
| Heisenberg | \(\operatorname{Heis}(\mathbb{Z}/p\mathbb{Z})\) · exponent \(p\) |
| Semidirect | \(\mathbb{Z}/p^2\mathbb{Z} \rtimes \mathbb{Z}/p\mathbb{Z}\) · exponent \(p^2\) |

**p = 2**

| Group | Structure |
|---|---|
| Cyclic | \(\mathbb{Z}/8\mathbb{Z}\) |
| Abelian | \(\mathbb{Z}/4\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}\) |
| Elementary abelian | \((\mathbb{Z}/2\mathbb{Z})^3\) |
| Dihedral | \(D_4\) (order 8) |
| Quaternion | \(Q_8\) (order 8) |

The main theorem is `P3Group.classification`:

```lean
theorem classification (G : Type*) [Group G] [Fintype G]
    (hcard : Nat.card G = p ^ 3) : IsP3Group p G
```

## Structure

| File | Content |
|---|---|
| `P3Group/Defs.lean` | Concrete group models: `CyclicP3`, `AbelianP2P`, `ElementaryP3`, `Heisenberg`, `SemidirectP2P` |
| `P3Group/Structural.lean` | Lemmas about p‑groups: center = \(p\), quotient center ≅ \((\mathbb{Z}/p)^2\), commutator = center, nilpotency class = 2 |
| `P3Group/AbelianCase.lean` | Classification of abelian groups of order \(p^3\) via the structure theorem |
| `P3Group/NonAbelianCase.lean` | Classification of non‑abelian groups of order \(p^3\); splits into \(p=2\) and odd \(p\), then by exponent |
| `P3Group/Classification.lean` | Main theorem + proof that the five types are pairwise non‑isomorphic |

## Build

```bash
lake build
```

Requirements: Lean 4 (`leanprover/lean4:v4.31.0` or later compatible).

## License

This project is licensed under the [Apache License 2.0](LICENSE).
