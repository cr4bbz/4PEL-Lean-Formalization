# Internes Peer-Review und Revisionsbericht

**Manuskript:** From Threshold Belief to Epistemic Phase Geometry: Mechanized
Dynamics in a Four-Valued Probabilistic Epistemic Logic.

**Autor:** Julian L. Voigt (cr4bbz). **Datum:** 7. September 2026.
**Begutachtete Fassung:** v0.3, Commit `680786b2236648159df66ccd8af366704706a36e`.
**Revision:** v0.4, Branch `research/modal-probabilistic-fine-graining`.

## 1. Art und Reichweite des Gutachtens

Dies ist ein internes, KI-gestütztes kritisches Review mit direkter Revision,
kein unabhängiges externes Peer-Review und keine Annahmeentscheidung einer
Zeitschrift. Geprüft wurden der vollständige Manuskripttext, die Darstellung
im PDF, die verwendeten semantischen Interfaces, die Hauptsatz-Deklarationen
und ihre tatsächlichen Axiom-Abhängigkeiten. Die Literaturprüfung war gezielt,
nicht systematisch oder vollständig. Insbesondere ersetzt sie keinen
Prioritätsnachweis und keine detaillierte Äquivalenzprüfung konkurrierender
Kalküle. Änderungen wurden im bestehenden Forschungsbranch vorgenommen;
es wurde kein neues Objektsprachen-System als bereits bewiesen ausgegeben.

Die Hauptfragen waren: Stimmen Prosa und Lean-Aussage überein? Welche
Voraussetzungen stehen nur im Code? Welche Aussagen sind elementare
Definitionsfolgen, welche echte Konstruktions- oder Negativresultate? Was
verifiziert der Build tatsächlich? Sind die Beispiele so beschrieben, dass
ein Leser die Begrenzungen ohne Repository-Recherche erkennen kann?

## 2. Gesamturteil

**Zur Fassung v0.3: Major revision.** Die untersuchte Beweiskette trägt eine
interessante mechanisierte Fallstudie. Die bisherige Darstellung war jedoch
noch nicht publikationsreif: zu spät offengelegte Modellannahmen, eine
missverständliche Dynamik-Metapher, fehlende direkte Literaturvorgänger und
eine unvollständige Auskunft über die Vertrauensbasis der Hauptsätze.

**Nach Revision:** Die konkreten Darstellungs- und Auditmängel sind wesentlich
behoben. Das Manuskript ist als überprüfbares Working Paper deutlich besser
abgegrenzt. Eine vorbehaltlose Empfehlung zur Journal-Einreichung ergibt sich
daraus nicht. Die mathematische Neuheit und die nachfolgend genannten
Realisierungsschritte bleiben eigenständige Aufgaben.

### Stärken

- Die Beweiskette verbindet eine konkrete Update-Familie mit einer expliziten
  Beobachtungsgeometrie; sie bleibt nicht bei verbalen Paradox-Diagnosen stehen.
- Die Quantifizierung der 16 Übergänge ist klar: eine parametrisierte Familie,
  nicht ein universell umsteuerbares einzelnes Modell.
- Die rationale Rechnung ist transparent und benötigt keine zusätzliche
  Analysis-Bibliothek. Die Zwischenphase hat einen expliziten Zeugen.
- Die Zuverlässigkeitsverfeinerung trennt Erhaltung und Informationsverlust.
  Insbesondere ist das S5-Gegenbeispiel hilfreich gegen eine Überinterpretation
  der Rahmenbedingungen.
- Der vorhandene Code trennt starke Wahrscheinlichkeitsintegrität bereits vom
  schwachen historischen Interface. Die Revision macht diese gute
  Architekturentscheidung nun auch früh im Text sichtbar.

## 3. Hauptkritik und direkte Umsetzung

### R1 — Modellvertrag ist schwächer als „endliches Wahrscheinlichkeitsmodell“

**Schwere: hoch.** `Model.mu` ist eine Funktion von Listen nach `Rat` mit nur
zwei Normalisierungspflichten. Nichtnegativität, Additivität, Extensionalität
und Duplikatfreiheit folgen daraus nicht. Außerdem ist `W` ein beliebiger Typ;
die gespeicherte Weltliste muss ihn nicht erschöpfen. Zugänglichkeitslisten
müssen nicht als Teilmenge dieser Weltliste zertifiziert sein. Der Ausdruck
„finite model“ verdeckte diese Unterschiede.

**Umgesetzt:** Abschnitt 2 beginnt jetzt mit dem schwachen Interface, benennt
die fehlenden Pflichten und unterscheidet es von `StrongProbabilityModel`.
Allgemeine Aussagen betreffen endliche Zugänglichkeitslisten; die konkreten
Beispiele benutzen tatsächlich endliche, abgeschlossene Weltuniversen.
Nichtleere Zugänglichkeit folgt schon aus der Normalisierung und wurde als
kleiner Kernel-Beweis nochmals explizit abgesichert. Das Interface selbst
wurde nicht inkompatibel umgebaut.

**Verbleibend:** Ein zusätzlicher Weltabschluss-/Finitheitsvertrag wäre für
spätere Modelltheorie sinnvoll, ist aber kein stillschweigendes Ergebnis dieser
Revision. Die starke Zertifizierung der bestehenden Reachability-Familie bleibt
eine separate Lean-Aufgabe.

### R2 — „Positive mass“ bedeutete im Code nur „nicht null“

**Schwere: hoch.** `ConditionalizationAdmissible.positive_mass` fordert
`conditionalizationEvidenceMass ≠ 0`. Im schwachen Interface darf eine
Nichtnullmasse negativ sein. Die bisherige Prosa sprach ohne Zusatz von
positiver Masse. Auch die Syntax des Update-Ereignisses war zu weit formuliert:
`conditionalize` benutzt die ältere `Formula`, nicht beliebige `ModalFormula`.

**Umgesetzt:** Abschnitt 3 nennt die genaue Nichtnullbedingung und erläutert,
dass erst Nichtnegativität daraus Positivität macht. Die beiden separaten
Normalisierungsfelder werden benannt. Die zulässige Ereignissyntax und die
Auswertung im Prior sind ausdrücklich beschrieben. Keine Umbenennung eines
öffentlichen Feldes wurde erzwungen und keine stärkere Updateintegrität
behauptet.

### R3 — Primitive K-Semantik und Faktorisierung wurden kausal verwechselt

**Schwere: hoch.** `modalKnowledgeValue` liest weder `mu` noch `c`. Es verwendet
nur die zugänglichen vollständigen Werte. Die Gleichung „K = stabilitätsgefiltertes
B“ ist trotzdem korrekt: Bei Homogenität sind die signierten Ereignisse leer
oder total, sodass Normalisierung die Schwellenwerte festlegt. Sie macht K
aber nicht zu einem Operator mit zwei unabhängigen probabilistischen Kanälen.

**Umgesetzt:** Abschnitt 2 gibt nun die positiven und negativen K-Klauseln,
einen Beweisabriss der Faktorisierung und die genaue Abhängigkeit an. Der neue
Satz `knowledge_ignores_probability_for_fixed_values` zeigt, dass bei gleicher
Zugänglichkeit und festem Werteprofil die Wahrscheinlichkeit irrelevant ist.
Dynamische K-Änderung kann über eingebettetes B entstehen. Der Abschnittstitel
„Two dynamic channels“ wurde entsprechend geändert.

„Knowledge“ bleibt der Name eines stipulierten Operators. Ohne Reflexivität
wird keine Faktivität am aktuellen Weltpunkt unterstellt. Auch eine reflexive
Glut ist nicht gleichbedeutend mit klassischer, ausschließlich wahrer Erkenntnis.

### R4 — Update-Endpunkte sind keine beobachtete zeitliche Trajektorie

**Schwere: hoch.** Ein diskretes Conditionalization-Paar liefert nicht automatisch
Zwischenzustände. Die Crossing-Sätze wählen zusätzlich den affinen Abschnitt
zwischen zwei Zahlenpaaren. Formulierungen wie „hidden phase history“ konnten
den Eindruck eines rekonstruierten tatsächlichen Update-Verlaufs erwecken.

**Umgesetzt:** Forschungsfrage, Abstract und Schluss wurden neu gefasst.
„Zeit“ bezeichnet ausdrücklich den Interpolationsparameter. Ein Wall Count
zählt verschiedene Endpunktbits, nicht Ereignisse auf beliebigen Kurven.
Die affine Notation im Korollar wird direkt als Endpunktinterpolation definiert.
Wahrscheinlichkeitszertifizierter Modellpfad, Formelsupport-Pfad und
Update-generierter Pfad werden getrennt.

**Zusätzliche Diagnose:** Auf festem endlichem Universum gibt es aus einem
festen Prior nur endlich viele ereignisbedingte Posteriors. Ein nichtkonstanter
rationaler affiner Gewichtsabschnitt hat unendlich viele Punkte. Daher ist eine
allgemeine Gleichsetzung nicht nur unbewiesen, sondern in dieser Lesart
unmöglich. Der Text kennzeichnet diesen einfachen mathematischen Einwand als
Beobachtung, nicht als neuen Lean-Satz. Soft-Evidence-Updates wären eine andere
Spezifikation.

### R5 — Gleichzeitige Schwellenhits haben einen übersehenen Randwert

**Schwere: mittel bis hoch.** Die Konvention lautet `c ≤ p`, nicht `c < p`.
Darum gehört `(c,c)` stets zu B. Bei simultanem T/F-Wechsel kann ein einzelner
B-Punkt auftreten, obwohl es keine offene Zwischenphase gibt.

**Umgesetzt:** `threshold_intersection_is_B` beweist den generischen Randwert.
`simultaneous_T_F_has_B_hit` prüft bei `c=3/5` den Abschnitt
`(4/5,2/5) → (2/5,4/5)` an den Parametern `0, 1/2, 1` mit den Werten `T,B,F`.
Abschnitt 8 trennt die offenen Phasen von den Crossing-Instanten. Auch Hits
am Intervallrand sind ausdrücklich zugelassen.

### R6 — „Stable“ bezeichnete zwei verschiedene Prädikate

**Schwere: hoch.** Das bestehende K prüft Homogenität innerhalb des
zugänglichen Bereichs. MPFGs `StableAt` vergleicht jede zugängliche Beobachtung
mit der Beobachtung am aktuellen Punkt. Auf nichtreflexiven Rahmen sind diese
Begriffe verschieden.

**Umgesetzt:** Im Kern steht die paarweise Homogenität als H. Im
MPFG-Abschnitt steht `Stable_cur`, und die Voraussetzung für die einfache
Identifikation wird benannt. Essence und Accident werden als klassische
Metaprädikate ausgeschrieben, einschließlich der möglichen Vakuosität von
Essence. Kein neues FDE-Negationsgesetz wird daraus gemacht.

### R7 — Build-Erfolg verschleierte Native-Axiom-Abhängigkeiten

**Schwere: hoch.** Der ursprüngliche MPFG-Audit deckte den älteren
Manuskriptkern nicht ab. Eine vollständiger ausgewählte Liste zeigte
Native-Decision-Axiome unter anderem in der K-Faktorisierung, den endlichen
Updatefamilien, Boolean-Wall-Hilfssätzen und Zwischenphasen. Ein allgemeiner
Satz kann solche Annahmen durch einen winzigen numerischen Hilfsbeweis erben.

**Umgesetzt:** 52 konkrete Manuskriptdeklarationen wurden in
`PEL4/PaperAxiomAudit.lean` enumeriert. In acht betroffenen Lean-Modulen wurden
Berechnungsbeweise auf `decide +kernel` umgestellt, ohne Theoremaussagen oder
Semantik zu ändern. Der neue CI-Checker verbietet alle Abhängigkeiten außer
`propext`, `Classical.choice` und `Quot.sound`. Er verwirft auch unvollständige,
leere oder doppelte Audit-Ausgaben. Sechs Unit-Tests prüfen seine
Fehlerpfade einschließlich `sorryAx` und Native-Axiomen.

**Ergebnis:** 52/52 ausgewählte Manuskriptdeklarationen: ausschließlich
Standard-Lean-Abhängigkeiten. Separater MPFG-Audit: 24/24. Die Aussage gilt
für diese Abhängigkeitsketten, nicht für das gesamte historische Repo.

### R8 — Direkte Literaturvorgänger fehlten

**Schwere: hoch für eine Publikation.** Klein, Majer und Rafiee Rad behandeln
bereits Wahrscheinlichkeiten mit Gaps/Gluts und Updatepolitiken. Bílková et al.
vergleichen signierte und vierregionige Wahrscheinlichkeitsdarstellungen.
Damit dürfen weder die probabilistische FDE-Basis noch die vier Zellen als
neuer Gegenstand des Projekts präsentiert werden. Der MPFG-Abschnitt nannte
seine direkten sechs- und vierwertigen Gesprächspartner bislang nicht im
Literaturverzeichnis.

**Umgesetzt:** Fünf einschlägige Einträge und konkrete Abgrenzungsabsätze
wurden ergänzt: probabilistische Vorgänger, zweischichtige Logiken,
sechswertige Evidenzlogiken, der Reliability-Preprint von 2026 und Petrukhins
Essence/Accident-Arbeit. Die sechs Szenarien werden nicht erst auf 2026 datiert.
Die veröffentlichte sechs-wertige Arbeit wird nach ihrem Version-of-record-Titel
zitiert. Belnaps Seitenangabe wurde nach dem Verlagsverzeichnis korrigiert.

**Verbleibend:** Eine theorematische Vergleichsmatrix mit Definitionen,
Übersetzungen und Nichtäquivalenzen. Die hinzugefügten Quellen begründen eine
vorsichtigere Positionierung, nicht Originalität.

### R9 — Die Tragweite elementarer Äquivalenzen war zu hoch gerahmt

**Schwere: mittel.** Die Schwellenrobustheit folgt unmittelbar aus
Koordinatengleichheit; die Ordnungstrichotomie aus linearer Ordnung; die
Faserzerlegung ist eine allgemeine Aussage über Abbildungen. Das macht die
Sätze nicht falsch oder nutzlos, aber auch nicht automatisch neu.

**Umgesetzt:** Der Text nennt diese elementare Natur und ergänzt Beweisabrisse
zu Faktorisierung, Reachability, affinen Hits und Projektionssätzen. Der
Beitrag wird in der mechanisierten Verbindung, den Verträgen und den
Informationsverlust-Zeugen verortet. „Klassifikation“ wird nicht mit einem
unabhängigen Verfahren zur Herstellung von Faserstarrheit verwechselt.

### R10 — Zuverlässigkeit ist hier eine Eingabe, keine begründete Eigenschaft

**Schwere: mittel.** Die sechs Zellen führen noch keinen
Klassizitätsoperator, keine Propagationsregeln und kein Lernverfahren ein.
Die ältere `EvidenceStatus`-Struktur erlaubt zudem mehr Kombinationen.

**Umgesetzt:** MPFG wird als Beobachtungsverfeinerung beschrieben, nicht als
voller LET-Kalkül. „Untagged“ bedeutet nicht „unreliable“. Erhaltung betrifft
die ausdrücklich definierten Beobachtungen, keine allgemeine
beweistheoretische Konservativität. Der Schluss nimmt MPFG nun in die
inhaltliche Zusammenfassung auf.

### R11 — Mehrdeutige Klassifikations- und Monotoniesprache

**Schwere: mittel.** Ohne benannte Ordnung ist „keine monotone
Wissensrichtung“ zu unspezifisch. Die kompositionelle Robustheit ist eine
hinreichende Zertifizierung, nicht die vollständige Charakterisierung aller
invarianten komplexen Formeln. „Unabhängige“ Evidenz könnte statistische
Unabhängigkeit suggerieren.

**Umgesetzt:** Die Aussage benennt die T/F-Zeugen; eine undefinierte
Informationsordnung wird nicht unterstellt. Robustheit wird als hinreichender
kompositioneller Vertrag bezeichnet. Unabhängigkeit heißt fehlende logische
Komplementarität, nicht stochastische Unabhängigkeit. Die Adjazenzgrafik hat
keine gerichteten Kanten mehr, die eine privilegierte Update-Richtung nahelegen.

### R12 — Manuskriptstruktur und Reproduzierbarkeit

**Schwere: mittel.** Der lange Abstract und die Schlusssektion wiederholten
die Entwicklung, ließen aber das neue MPFG-Ergebnis aus. Der Korrespondenzanhang
enthielt abgekürzte Namen und deckte MPFG nicht ab. Die doppelte Modultabelle
erhöhte den Platzbedarf ohne zusätzlichen Beweisgehalt.

**Umgesetzt:** Abstract und Schluss wurden ersetzt, die doppelte Tabelle
entfernt, MPFG und die Review-Randsätze in den Anhang aufgenommen und die
unbestimmten Namensabkürzungen ausgeschrieben. Der Vertrauensstatus verweist
auf ein explizites Inventar. Version, Autorzeile und Reproduktionsanweisungen
wurden aktualisiert. Ein zusätzlicher Paper-Check rendert die Quellen, prüft
Überläufe und Referenz-/Schriftfehler und vergleicht in CI den extrahierten
Text des eingecheckten PDFs mit dem frischen Render. Das ersetzt keine
visuelle Layoutprüfung, verhindert aber viele veraltete PDF-Stände.

## 4. Nicht durch Textrevision erledigte Forschungsaufgaben

1. **Strong promotion der Reachability-Familie:** Die konkret gemeinten
   Prior-/Posterior-Maße sind plausibel gewöhnliche finite Maße; benötigt wird
   ihr exakter Lean-Nachweis im stärkeren Vertrag.
2. **Formula-level model-path lift:** Für atomare bzw. geeignete
   wahrscheinlichkeitsfreie Formeln müssen unveränderliche Ereignismengen mit
   dem affinen Maßsatz verbunden werden. Für beliebiges verschachteltes B
   folgt die Behauptung nicht.
3. **Update-generierte Pfade:** Ein anderes Updatekonzept oder eine präzise
   eingeschränkte Existenzfrage ist nötig; ereignisbedingte Updates eines
   festen endlichen Priors können keinen beliebigen nichtkonstanten affinen
   Pfad vollständig durchlaufen.
4. **Begründete Zuverlässigkeit:** Tags müssen erst durch eine explizite
   Quellen-/Kalibrierungs-/Evidenzsemantik gerechtfertigt werden, wenn mehr als
   eine Datenverfeinerung beansprucht wird.
5. **Publikationspositionierung:** Vergleich mit den direkten Vorarbeiten,
   möglichst anhand gleicher Minimalbeispiele und tatsächlicher Übersetzungen.
   Ein passender Beitrag kann ein Formalisierungs-/Artefaktpapier sein; ein
   neuer großer Logikkalkül wird hier nicht geliefert.

## 5. Validierung und nachvollziehbare Evidenz

Die formalen Änderungen einschließlich der Kernel-Umstellungen wurden in
[CI 34133500237](https://github.com/cr4bbz/4PEL-Lean-Formalization/actions/runs/34133500237)
für Commit `07fbc5193e0f7e43de565158c0eaf0cbb9c08dfb` geprüft:

- `lake build`: erfolgreich, 122 Jobs.
- Manuskript-Audit: `PAPER_AXIOMS_OK declarations=52 standard=52 native=0`.
- MPFG-Audit: 24 Deklarationen erfolgreich unter dem strikten Whitelist-Vertrag.
- Sechs Audit-Checker-Tests erfolgreich.
- Das deklarationsweise Inventar steht in `PAPER_AXIOMS_v0.4.json`.

Die lokale Lean-Ausführung scheitert in dieser Arbeitsumgebung an der
Ermittlung des Installationspfads. Deshalb stammt die neue formale
Validierung ausdrücklich aus GitHub Actions, nicht aus einem behaupteten
lokalen Lean-Lauf. Der lokale LaTeX-Render erzeugt 27 Seiten ohne übervolle
Boxen, undefinierte Referenzen oder Schriftwarnungen. Alle 27 Seiten wurden
zusätzlich visuell geprüft. Der neue CI-Schritt vergleicht den extrahierten
PDF-Text mit einem frischen Render; Layoutgleichheit wird damit nicht behauptet.

## 6. Quellen und Prüfungstiefe

- Klein, Majer, Rafiee Rad (2021): [Verlagsseite und Abstract](https://doi.org/10.1007/s10992-021-09592-x).
  Abgesichert: probabilistische BD-Erweiterung, Axiomatisierung, Bayes/Jeffrey
  und Aggregation. Keine Gleichsetzung mit dem aktuellen K vorgenommen.
- Bílková et al. (2025): [Version of record](https://doi.org/10.1017/S0960129525000064),
  [zugänglicher Preprint, Einführung und Begriffe](https://arxiv.org/html/2402.12953v3).
  Abgesichert: signierte versus vierregionige Darstellung, zweischichtige
  Logiken; kein vollständiger Beweisvergleich im Rahmen dieses Reviews.
- Coniglio/Rodrigues (2024, online 2023): [Verlagsseite](https://doi.org/10.1007/s11225-023-10062-5),
  [Preprinttext](https://arxiv.org/html/2209.12337v2).
  Abgesichert: sechs Szenarien, Klassizitätsoperator und Propagationsregeln;
  MPFGs reine Tag-Semantik erfüllt damit noch keinen LET-Kalkül.
- Borja Macias/Coniglio/Hernández-Tello (2026): [arXiv-Abstract](https://arxiv.org/abs/2608.20228).
  Hier ausdrücklich nur Abstractprüfung; nicht vollständig nachformalisiert.
- Petrukhin (2026): [Verlagsabstract](https://doi.org/10.1007/s11225-026-10250-z).
  Abgesichert: Objektsprachenmodalitäten, S5-Semantik, Hypersequenzen;
  kein Kalkültransfer auf unsere Metaprädikate behauptet.
- Belnap (1977): [Verlagskapitel](https://doi.org/10.1007/978-94-010-1161-7_2).
  Bibliografische Prüfung: Seiten 5–37.
- Lean 4.31-Quellen, insbesondere `Lean/Meta/Native.lean`: der native Taktikpfad
  erzeugt Axiome über berechnete Bool-Werte. Der neue strikte Checker lehnt sie
  in den ausgewählten Beweisketten ab, statt sie als Standardlogik zu verbuchen.

## 7. Empfehlung für das nächste externe Gutachten

Eine externe Gutachterin sollte zuerst die expliziten Verträge und die drei
Ebenen (Update-Endpunkte, Supportinterpolation, zertifizierter Modellpfad)
prüfen. Danach sind Reichweite und Neuheit der Kombination zu beurteilen.
Die sinnvolle Leitfrage ist nicht „Hat Lean das Paper akzeptiert?“, sondern:
„Sind genau die für die wissenschaftliche Behauptung nötigen Voraussetzungen
formalisiert, und unterscheidet sich das Ergebnis hinreichend von seinen
Vorgängern?“ Die Revision verbessert die Beantwortbarkeit dieser Frage,
nimmt ihre endgültige Antwort aber nicht vorweg.
