# Paper review after Gate 21

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 21. It is a currency and claim-scope review, not an
independent external peer review.

## Overall judgment

Gate 21 supplies the finite localization bridge that Gate 20 left open. A
fixed formula over explicit finite roots has an exact finite recovery-
observation map, and every recovery change under conditionalization has a
changed belief-result entry in that map. The manuscript remains internally defensible but
substantially behind the Lean development, whose theorem narrative now extends
twelve gates beyond the current Gate-9 endpoint.

## Findings by priority

### High: present the compiler as exact, not heuristic

The compiled list is not merely a debugging trace or a convenient
over-approximation. Lean proves that all its observations are classical if and
only if the recursive semantic classicality certificate holds. Under
probability integrity this is exactly recovery on the selected roots.

### High: preserve the finite-root/global distinction

The base model does not assert that `m.worlds` covers the entire type `W`.
Claims about a finite map therefore apply directly to `CompositionalRecoveryOn`
for explicit roots. They lift to globally quantified recovery only when a
`WorldListCovers` proof is supplied. Omitting this guard would overstate the
formal result.

### High: localization is not yet a flip-count bound

Every recovery change now has a finite belief-observation witness, but Gate 21 does
not prove that each witness consumes a fresh unit of Gate-20 scope budget. A
subsequent theorem must show that a changed belief observation requires strict
cumulative support loss and must account for repeated use of duplicated sites.

### Medium: duplicates have semantic provenance

The compiler deliberately retains repeated world/formula pairs when they arise
through different recursive paths or roots. The Gate-19 count of twenty is a
count of observation positions, not necessarily twenty distinct pairs after
quotienting.

## Recommended manuscript placement

Place Gate 21 after the Gate-20 local resource inequality. The presentation
should use the sequence:

```text
local finite resource bound
-> exact finite recovery-observation map
-> stuttering theorem
-> changed-observation localization
-> open numerical aggregation theorem.
```

The twenty-position Gate-19 instance is suitable as an illustration, provided
the paper states that duplicates are retained and that no global flip number
has yet been proved.

## Layout status

Gate 21 changes no TeX source. The committed manuscript remains version 0.13
and 54 pages. Integration belongs in a deliberate version-0.14 revision with
a fresh render and visual review.

## Editorial decision

Gate 21 is suitable for manuscript integration. Its exact compiler and
contrapositive localization theorem materially strengthen the finite-update
story, while its coverage condition and unproved aggregation step keep the
scope scientifically honest.
