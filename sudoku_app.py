import json
import time
from pathlib import Path

import streamlit as st

from sudoku_solver import (
    atom,
    build_definite_kb,
    build_general_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails,
)


APP_DIR = Path(__file__).resolve().parent


def load_pool():
    with (APP_DIR / 'puzzles.json').open(encoding='utf-8') as handle:
        raw = json.load(handle)
    return raw


def decode_cells(mapping):
    return {tuple(int(part) for part in key.split('_')): value
            for key, value in mapping.items()}


def render_grid(n, box_h, box_w, values, givens):
    cells = []
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            value = values.get((r, c), '')
            kind = 'given' if (r, c) in givens else (
                'solved' if value != '' else 'empty')
            right = ' thick-right' if c % box_w == 0 and c < n else ''
            bottom = ' thick-bottom' if r % box_h == 0 and r < n else ''
            cells.append(
                f'<div class="cell {kind}{right}{bottom}">{value}</div>')

    st.markdown(
        f'''
        <style>
        .sudoku-grid {{
            display:grid; grid-template-columns:repeat({n}, minmax(34px, 54px));
            width:fit-content; border:3px solid #172554; border-radius:8px;
            overflow:hidden; box-shadow:0 8px 24px rgba(15,23,42,.10);
            margin:.4rem 0 1rem 0;
        }}
        .cell {{
            aspect-ratio:1; display:flex; align-items:center; justify-content:center;
            font-size:1.25rem; border-right:1px solid #cbd5e1;
            border-bottom:1px solid #cbd5e1; color:#0f172a; background:white;
        }}
        .given {{font-weight:800; color:#1d4ed8; background:#eff6ff;}}
        .solved {{font-weight:650; color:#047857; background:#f0fdf4;}}
        .empty {{color:#94a3b8; background:#f8fafc;}}
        .thick-right {{border-right:3px solid #172554;}}
        .thick-bottom {{border-bottom:3px solid #172554;}}
        </style>
        <div class="sudoku-grid">{''.join(cells)}</div>
        ''',
        unsafe_allow_html=True,
    )


def parse_atom(symbol):
    text = str(symbol)
    prefix = 'Not' if text.startswith('Not') else 'Is'
    coordinates = text[len(prefix):]
    r, c, v = (int(part) for part in coordinates.split('_'))
    return prefix, r, c, v


def explain_trace_item(item, box_h, box_w):
    prefix, r, c, v = parse_atom(item['goal'])
    premises = item['premises']

    if item['kind'] == 'fact':
        return f'Cell ({r}, {c}) = {v} is an initial given.'

    if prefix == 'Is' and premises:
        excluded = sorted(parse_atom(premise)[3] for premise in premises)
        return (
            f'Cell ({r}, {c}) cannot be {", ".join(map(str, excluded))}; '
            f'therefore {v} is its last remaining candidate.')

    if prefix == 'Not' and len(premises) == 1:
        _, source_r, source_c, source_v = parse_atom(premises[0])
        if (source_r, source_c) == (r, c):
            reason = f'the cell is already fixed as {source_v}'
        elif source_r == r:
            reason = f'row {r} already contains {source_v} at column {source_c}'
        elif source_c == c:
            reason = f'column {c} already contains {source_v} at row {source_r}'
        else:
            source_box = ((source_r - 1) // box_h, (source_c - 1) // box_w)
            target_box = ((r - 1) // box_h, (c - 1) // box_w)
            reason = (
                f'the same box already contains {source_v} at '
                f'({source_r}, {source_c})'
                if source_box == target_box else 'a Sudoku constraint excludes it')
        return f'Eliminate {v} from cell ({r}, {c}) because {reason}.'

    return f'Established {prefix}({r}, {c}, {v}) from its required premises.'


st.set_page_config(page_title='Sudoku Logic Tutor', page_icon='🧩', layout='wide')
st.title('🧩 Sudoku Logic Tutor')
st.caption('Solve Sudoku with propositional-logic forward or backward chaining.')

pool = load_pool()
n, box_h, box_w = pool['n'], pool['box_h'], pool['box_w']
puzzle_index = st.selectbox(
    'Choose a puzzle',
    range(len(pool['puzzles'])),
    format_func=lambda index: (
        f'Puzzle {index + 1} - '
        f'{pool["puzzles"][index]["given_count"]} givens'),
)
puzzle = pool['puzzles'][puzzle_index]
givens = decode_cells(puzzle['givens'])

board_column, control_column = st.columns([1.25, 1], gap='large')

with board_column:
    st.subheader('Puzzle board')
    render_grid(n, box_h, box_w, givens, givens)
    st.caption('Blue cells are the original givens; green cells are inferred.')

with control_column:
    st.subheader('Full-grid solver')
    algorithm = st.radio(
        'Inference algorithm',
        ('Forward chaining', 'Backward chaining'),
        horizontal=True,
    )
    if st.button('Solve the full grid', type='primary', use_container_width=True):
        solver = (solve_full_grid_fc if algorithm == 'Forward chaining'
                  else solve_full_grid_bc)
        with st.spinner(f'Running {algorithm.lower()}...'):
            started = time.perf_counter()
            try:
                solved = solver(n, box_h, box_w, givens)
            except ValueError as error:
                st.error(str(error))
            else:
                elapsed = time.perf_counter() - started
                st.session_state['solved_result'] = (
                    puzzle_index, solved, algorithm, elapsed)

    result = st.session_state.get('solved_result')
    if result and result[0] == puzzle_index:
        _, solved, used_algorithm, elapsed = result
        st.success(f'{used_algorithm} solved the puzzle in {elapsed:.3f} seconds.')
        render_grid(n, box_h, box_w, solved, givens)

st.divider()
st.subheader('Targeted entailment query')
st.write('Ask whether a particular cell value follows from the Horn knowledge base.')
query_columns = st.columns(4)
with query_columns[0]:
    query_r = st.number_input('Row', 1, n, 1, 1)
with query_columns[1]:
    query_c = st.number_input('Column', 1, n, 1, 1)
with query_columns[2]:
    query_v = st.number_input('Value', 1, n, 1, 1)
with query_columns[3]:
    st.write('')
    st.write('')
    run_query = st.button('Check entailment', use_container_width=True)

if run_query:
    with st.spinner('Building the knowledge base and tracing the proof...'):
        kb = build_definite_kb(n, box_h, box_w, givens)
        trace = []
        verdict = pl_bc_entails(
            kb, atom('Is', int(query_r), int(query_c), int(query_v)), trace)

    if verdict:
        st.success(
            f'True - the KB entails that cell ({query_r}, {query_c}) = {query_v}.')
        st.subheader('Tutor-mode reasoning trace')
        explanations = []
        seen = set()
        for item in trace:
            text = explain_trace_item(item, box_h, box_w)
            if text not in seen:
                seen.add(text)
                explanations.append(text)
        visible_limit = 120
        for step, explanation in enumerate(explanations[:visible_limit], 1):
            with st.expander(f'Step {step}', expanded=step <= 3):
                st.write(explanation)
        if len(explanations) > visible_limit:
            st.info(
                f'The proof contains {len(explanations)} deductions. '
                f'The first {visible_limit} are displayed.')
    else:
        st.warning(
            f'False - the KB does not entail that cell '
            f'({query_r}, {query_c}) = {query_v}.')
        st.info(
            'Backward chaining exhausted all rules capable of supporting '
            'this query, so no valid proof chain was found.')
