# Documents for AI Readers · [中文版](README.zh-CN.md)

[Repository home](../README.md)

This directory collects onboarding guides, design requirements, methodological notes, and handoff documents intended for AI agents joining the project. Each topic is available as a complete English document and a Chinese counterpart, with language-switching and reference links.

These are reading materials, not an `AGENTS.md` configuration or an additional collection of formally verified theorems. A design preference, a conditional argument, a research conjecture, and an implemented or formalized result must remain clearly distinguished.

## Reading list

1. **Designing Beautiful Fundamental-Sequence Ordinal Notations** — [English](fundamental-sequence-aesthetics.md) · [中文](fundamental-sequence-aesthetics.zh-CN.md). The first guide, addressed to a new GPT‑6 Astra agent without extensive prior knowledge of ordinal notations. It explains column-based syntax, last-column expansion, prefix-nested fundamental sequences, compatible reachable domains, exact local count sequences and lexicographic comparison, simple column contents, substantive increases in strength, proof obligations, and delivery expectations. It includes the count-sequence argument, examples, a checklist, and a ready-to-share task brief.

## Two practical destinations

- **[The user's GitHub repository](https://github.com/hzyhhzy/column-ordinal-notations-hzy)** is a source of notation definitions, implementations, and proof ideas. Start with the [repository overview](../README.md), then consult the [paper proofs](../proofs/paper/) and [Lean documentation](../lean/README.md). Reference material is not a requirement to copy an existing system or remain within its strength.
- **[NER / ne-rewritten](https://smilelee-lyx.github.io/ne-rewritten/)** is where the user intends to inspect and expand completed notation systems. A browser-facing delivery should therefore include a JavaScript expander compatible with its custom-notation interface, with suitable structural and count-sequence displays. A paper or Python core alone does not complete that interface work. The mathematical rules remain independent of the website.

## Adding another document

- Give each topic its own descriptive filename: `topic-name.md` for English and `topic-name.zh-CN.md` for Chinese. Keep both versions substantively complete and synchronized.
- Put a link to the other language in the first heading, and provide links back to this index and to relevant definitions, proofs, or tools.
- Add the topic to both versions of this reading list. Use relative links for repository files and explicit HTTPS links for outside resources; do not include machine-specific paths.
- State the intended reader, purpose, prerequisites, date or version, and the boundary between established results and proposals. Preserve distinctions such as structurally legal inputs versus standard reachable expressions.
- Keep design guidance here; put a notation's actual definition and expander under `notations/`, research comparisons under `research/`, and proof artifacts under their existing directories. A new guide does not alter those artifacts or their proof status.
- Markdown is sufficient for this collection; adding a topic does not by itself require a PDF or a new Lean project. Run `python tools/check_release.py` from the repository root to check language pairs and local links alongside the existing release checks.

The collection currently contains one topic in two languages. Future AI-facing documents can be added independently without changing existing notation implementations or proofs.
