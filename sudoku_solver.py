"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


class _IndexedPropDefiniteKB(PropDefiniteKB):
    """PropDefiniteKB with a premise index for practical FC performance."""

    def __init__(self):
        self._premise_index = {}
        self._inferred_symbols = set()
        super().__init__()

    def tell(self, sentence):
        super().tell(sentence)
        if sentence.op == '==>':
            for premise in conjuncts(sentence.args[0]):
                self._premise_index.setdefault(premise, []).append(sentence)

    def clauses_with_premise(self, premise):
        # pl_fc_entails calls this exactly when it processes an inferred
        # symbol, which lets a full saturation run expose its closure.
        self._inferred_symbols.add(premise)
        return self._premise_index.get(premise, [])


def _implication(premises, conclusion):
    """Construct a definite clause from one or more positive premises."""
    return Expr('==>', associate('&', premises), conclusion)


def _peers(n, box_h, box_w, r, c):
    """Return every cell sharing a row, column, or box with (r, c)."""
    peers = set()
    for other in range(1, n + 1):
        if other != c:
            peers.add((r, other))
        if other != r:
            peers.add((other, c))

    box_row = ((r - 1) // box_h) * box_h + 1
    box_col = ((c - 1) // box_w) * box_w + 1
    for rr in range(box_row, box_row + box_h):
        for cc in range(box_col, box_col + box_w):
            if (rr, cc) != (r, c):
                peers.add((rr, cc))
    return peers


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    kb = PropKB()
    # Every sentence below is already a single CNF clause. Appending it
    # directly avoids repeatedly converting thousands of clauses to CNF.
    add_clause = kb.clauses.append

    # Every cell has at least one value.
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            add_clause(associate('|', [atom('Is', r, c, v)
                                       for v in range(1, n + 1)]))

    # Every cell has at most one value.
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v1 in range(1, n + 1):
                for v2 in range(v1 + 1, n + 1):
                    add_clause(~atom('Is', r, c, v1) |
                               ~atom('Is', r, c, v2))

    # A value cannot occur twice in a row.
    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(c1 + 1, n + 1):
                    add_clause(~atom('Is', r, c1, v) |
                               ~atom('Is', r, c2, v))

    # A value cannot occur twice in a column.
    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(r1 + 1, n + 1):
                    add_clause(~atom('Is', r1, c, v) |
                               ~atom('Is', r2, c, v))

    # A value cannot occur twice in a box.
    for box_row in range(1, n + 1, box_h):
        for box_col in range(1, n + 1, box_w):
            cells = [(r, c)
                     for r in range(box_row, box_row + box_h)
                     for c in range(box_col, box_col + box_w)]
            for v in range(1, n + 1):
                for i in range(len(cells)):
                    for j in range(i + 1, len(cells)):
                        r1, c1 = cells[i]
                        r2, c2 = cells[j]
                        add_clause(~atom('Is', r1, c1, v) |
                                   ~atom('Is', r2, c2, v))

    # The given cells hold their stated values.
    for (r, c), v in givens.items():
        add_clause(atom('Is', r, c, v))

    return kb


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    kb = _IndexedPropDefiniteKB()

    # Givens are the initial positive facts.
    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            peers = _peers(n, box_h, box_w, r, c)
            for v in range(1, n + 1):
                is_value = atom('Is', r, c, v)

                # At most one value in this cell.
                for other_v in range(1, n + 1):
                    if other_v != v:
                        kb.tell(_implication(
                            [is_value], atom('Not', r, c, other_v)))

                # Row, column, and box uniqueness via candidate elimination.
                for peer_r, peer_c in peers:
                    kb.tell(_implication(
                        [is_value], atom('Not', peer_r, peer_c, v)))

                # If every alternative is eliminated, v is the last candidate.
                alternatives = [atom('Not', r, c, other_v)
                                for other_v in range(1, n + 1)
                                if other_v != v]
                kb.tell(_implication(alternatives, is_value))

    return kb


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solved = dict(givens)

    # Ask for a symbol that has no defining rule. The provided
    # pl_fc_entails therefore runs its agenda to exhaustion, while the
    # indexed KB records the complete set of inferred propositions. This is
    # one shared forward-chaining pass instead of restarting it per query.
    pl_fc_entails(kb, expr('SudokuClosureSentinel'))
    closure = kb._inferred_symbols

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in solved:
                continue
            for v in range(1, n + 1):
                if atom('Is', r, c, v) in closure:
                    solved[(r, c)] = v
                    break
            if (r, c) not in solved:
                raise ValueError(
                    f'Forward chaining could not solve cell ({r}, {c})')
    return solved


def pl_bc_entails(kb, query, trace=None):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    # Build reusable indexes without changing the logical content of the KB.
    if not hasattr(kb, '_bc_facts'):
        facts = set()
        rules = {}
        for clause in kb.clauses:
            premises, conclusion = parse_definite_clause(clause)
            if premises:
                rules.setdefault(conclusion, []).append(tuple(premises))
            else:
                facts.add(conclusion)
        universe = set(facts)
        for conclusion, candidate_rules in rules.items():
            universe.add(conclusion)
            for premises in candidate_rules:
                universe.update(premises)
        kb._bc_facts = facts
        kb._bc_rules = rules
        kb._bc_universe = universe
        kb._bc_true_cache = set(facts)
        kb._bc_false_cache = set()
        kb._bc_provenance = {}
        kb._bc_complete = False

    facts = kb._bc_facts
    rules = kb._bc_rules
    true_cache = kb._bc_true_cache
    false_cache = kb._bc_false_cache
    provenance = kb._bc_provenance

    def append_trace_for(goal):
        """Reconstruct only the successful proof, in premise-first order."""
        if trace is None:
            return
        emitted = set()

        def emit(current):
            if current in emitted:
                return
            emitted.add(current)
            if current in facts:
                trace.append({'kind': 'fact', 'goal': current,
                              'premises': ()})
                return
            premises = provenance.get(current, ())
            for premise in premises:
                emit(premise)
            trace.append({'kind': 'rule', 'goal': current,
                          'premises': premises})

        emit(goal)

    if query in true_cache:
        append_trace_for(query)
        return True
    if query in false_cache:
        return False
    if kb._bc_complete:
        return False

    # Recursively collect only rules that can contribute to this goal. The
    # visited table cuts cycles; the subsequent fixed point gives tabled
    # backward chaining its sound least-model interpretation.
    relevant_goals = set()
    relevant_rules = []

    goal_stack = [query]
    while goal_stack:
        goal = goal_stack.pop()
        if goal in relevant_goals:
            continue
        relevant_goals.add(goal)
        for premises in rules.get(goal, ()):
            relevant_rules.append((premises, goal))
            goal_stack.extend(premises)

    known = {goal for goal in relevant_goals if goal in true_cache}
    waiting = {}
    remaining = {}
    agenda = list(known)

    for index, (premises, conclusion) in enumerate(relevant_rules):
        if conclusion in known:
            continue
        missing = [premise for premise in premises if premise not in known]
        remaining[index] = len(missing)
        if not missing:
            known.add(conclusion)
            provenance.setdefault(conclusion, premises)
            agenda.append(conclusion)
        else:
            for premise in missing:
                waiting.setdefault(premise, []).append(index)

    processed = set()
    while agenda:
        established = agenda.pop()
        if established in processed:
            continue
        processed.add(established)
        for index in waiting.get(established, ()):
            if remaining[index] == 0:
                continue
            remaining[index] -= 1
            if remaining[index] == 0:
                premises, conclusion = relevant_rules[index]
                if conclusion not in known:
                    known.add(conclusion)
                    provenance.setdefault(conclusion, premises)
                    agenda.append(conclusion)

    true_cache.update(known)
    if relevant_goals == kb._bc_universe:
        kb._bc_complete = True
        false_cache.update(kb._bc_universe - true_cache)
    if query in known:
        append_trace_for(query)
        return True

    false_cache.add(query)
    return False


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solved = dict(givens)

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in solved:
                continue
            for v in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    solved[(r, c)] = v
                    break
            if (r, c) not in solved:
                raise ValueError(
                    f'Backward chaining could not solve cell ({r}, {c})')
    return solved
