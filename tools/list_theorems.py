"""List every theorem of the game, by the mode it is used in and the tab it is filed under.

Reads the built game data (`lake build` first) and writes `THEOREMS.md` beside the
README. Usage: `py -3 tools/list_theorems.py`

A theorem whose statement is an equation is a rule of Rewrite Mode, under the tab
`TheoremDoc … in "…"` names. Any other theorem is a card of Proposition Mode's lower
menu, whose tabs Visual Lean works out itself (`theoremBucket` in lean4game's
`client/src/visual/theoremOrdering.ts`, which `bucket` below follows).
"""
import io
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA = os.path.join(ROOT, '.lake', 'gamedata')
REWRITE_TABS = ['+', '*', '^', '≤', '012', 'Peano']
# The theorems the game keeps on the Peano tab (`VisualPeanoTab`), read from game.json.
PEANO_TAB = set()
PROPOSITION_TABS = [('peano', 'Peano'), ('add', '+'), ('ne', '≠'), ('le', '≤'), ('gt', '>'), ('mul', '*'), ('other', 'Other')]


def load(name):
    with io.open(os.path.join(DATA, name), encoding='utf-8') as handle:
        return json.load(handle)


def split_statement(statement):
    """` (a b : ℕ) (h : a = b) : a ≤ b` → premises `['a = b']` and conclusion `a ≤ b`."""
    text, premises, depth, start, index = statement.strip(), [], 0, None, 0
    while index < len(text):
        char = text[index]
        if char == '(':
            if depth == 0:
                start = index
            depth += 1
        elif char == ')':
            depth -= 1
            if depth == 0:
                names, _, kind = text[start + 1:index].partition(' : ')
                if not re.fullmatch(r'ℕ|Prop|ℕ → ℕ', kind.strip()):
                    premises += [kind.strip()] * len(names.split())
        elif char == ':' and depth == 0:
            break
        index += 1
    conclusion = text[index + 1:].strip()
    # `∀ a b : ℕ, …`: the numbers are fixed with a click, like any other theorem's.
    while True:
        leading = re.match(r'∀\s*(?:\([^()]*:\s*ℕ\)\s*|[^,():]+:\s*ℕ\s*)+,\s*', conclusion)
        if not leading:
            break
        conclusion = conclusion[leading.end():]
    return premises, conclusion


def successors(text):
    """`MyNat.S (a + b)` and `MyNat.S a` as Visual Lean shows them, `S(a + b)` and `S(a)`."""
    text = re.sub(r'MyNat\.S (\w+)', r'S(\1)', text)
    return text.replace('MyNat.S (', 'S(')


def display(statement):
    premises, conclusion = split_statement(statement)
    bracket = lambda premise: f'({premise})' if re.search(r'[→↔]', premise) else premise
    return successors(' → '.join([bracket(premise) for premise in premises] + [conclusion]))


def world_order(game):
    """The worlds in an order that respects the map's paths, and is otherwise by name."""
    nodes, edges = sorted(game['worlds']['nodes']), game['worlds']['edges']
    order = []
    while len(order) < len(nodes):
        ready = [world for world in nodes if world not in order
                 and all(source in order for source, target in edges if target == world)]
        order.append(ready[0] if ready else next(world for world in nodes if world not in order))
    return order


def bucket(name, category, proposition):
    base = name.split('.')[-1]
    searchable = f'{name} {base} {proposition}'
    token = lambda words: re.search(rf'(?:^|[._\s])(?:{words})(?:[._\s]|$)', searchable)
    if base in PEANO_TAB or (category == 'Peano' and base in ('reflection', 'peano_cases')):
        return 'peano'
    if category == '*' or token('mul') or '*' in searchable:
        return 'mul'
    if category == '+':
        return 'add'
    if category == '≤':
        return 'le'
    if category == '>':
        return 'gt'
    if category == '≠':
        return 'ne'
    if token('reflection|succ_inj') or token('add') or '+' in searchable:
        return 'add'
    if token('le') or '≤' in searchable:
        return 'le'
    if token('ne') or '≠' in searchable:
        return 'ne'
    return 'other'


def main():
    game = load('game.json')
    PEANO_TAB.update(name.split('.')[-1] for name in game.get('visualPeanoTab', []))
    worlds = game['worlds']['nodes']
    axioms = {name.split('.')[-1] for name in game.get('visualAxioms', [])}
    order = world_order(game)
    # Where each theorem comes from: every level lists the theorems the player has by
    # then, each with the level that proved it or handed it out.
    source = {}
    for world in order:
        for index in range(1, game['worldSize'][world] + 1):
            for entry in load(f'level__{world}__{index}.json')['lemmas']:
                if entry.get('world') and entry['name'] not in source:
                    source[entry['name']] = (entry['world'], entry['level'])
    # A theorem that nothing after its level lists (the last level of a path's end).
    for world in order:
        for index in range(1, game['worldSize'][world] + 1):
            source.setdefault(load(f'level__{world}__{index}.json').get('statementName') or '', (world, index))

    rows = []
    for entry in load('inventory.json')['lemmas']:
        doc = load(f"doc__Theorem__{entry['name']}.json")
        where, rank = 'never', (len(order), 0)
        if entry['name'] in source:
            world, index = source[entry['name']]
            level = load(f'level__{world}__{index}.json')
            label = level.get('visualLevelNumber') or str(index)
            proved = level.get('statementName') == entry['name']
            where = f"{'after' if proved else 'from'} {worlds[world].get('title') or world} {label}"
            rank = (order.index(world), index)
        shown = display(doc['statement'])
        rows.append({
            'name': doc['displayName'], 'kind': doc.get('theoremKind'), 'category': doc.get('category') or '',
            'statement': shown, 'where': where, 'rank': rank,
            'bucket': bucket(entry['name'], doc.get('category') or '', shown),
            'axiom': doc['displayName'] in axioms,
        })
    rows.sort(key=lambda row: (row['rank'], row['name']))

    lines = ['# Theorems', '', 'Written by `tools/list_theorems.py` from the built game. A number in a statement',
             'is any number: a theorem is about all of them. “after” a level: proved there, and',
             'yours once it is done. “from” a level: handed out there.', '']
    def table(title, chosen):
        if not chosen:
            return
        lines.extend([f'### {title}', '', '| Theorem | Statement | Yours |', '|---|---|---|'])
        for row in chosen:
            name = f"`{row['name']}`" + (' (axiom)' if row['axiom'] else '')
            lines.append(f"| {name} | `{row['statement']}` | {row['where']} |")
        lines.append('')

    rewrite = [row for row in rows if row['kind'] == 'equality']
    proposition = [row for row in rows if row['kind'] != 'equality']
    lines.extend([f'## Rewrite Mode ({len(rewrite)} rules)', ''])
    tabs = REWRITE_TABS + sorted({row['category'] for row in rewrite} - set(REWRITE_TABS))
    for tab in tabs:
        table(f'Tab `{tab}`' if tab else 'No tab', [row for row in rewrite if row['category'] == tab])
    lines.extend([f'## Proposition Mode ({len(proposition)} cards)', ''])
    for key, label in PROPOSITION_TABS:
        table(f'Tab `{label}`' if key != 'other' else 'The tab for the rest (named after what the game files them under)',
              [row for row in proposition if row['bucket'] == key])
    with io.open(os.path.join(ROOT, 'THEOREMS.md'), 'w', encoding='utf-8', newline='\n') as handle:
        handle.write('\n'.join(lines))
    print(f'{len(rewrite)} rules of Rewrite Mode, {len(proposition)} cards of Proposition Mode')


if __name__ == '__main__':
    main()
