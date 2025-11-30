import subprocess
from argparse import ArgumentParser
import time

NEXT_VAR_ID = 1

def load_instance(input):
    GRID_SIZE = int(input)
    return GRID_SIZE
 
def encode(n, target_pop):
    global NEXT_VAR_ID
    NEXT_VAR_ID = 1
    cnf = []

    grid_vars = [[new_var() for column in range(n)] for row in range(n)]

    for row in range(n):
        for column in range(n):
            neighbours = []
            for d_row in [-1, 0, 1]:
                for d_column in [-1, 0, 1]:
                    if d_row == d_column == 0: continue
                    n_row = row + d_row
                    n_column = column + d_column
                    if 0 <= n_row < n and 0 <= n_column < n:
                        neighbours.append(grid_vars[n_row][n_column])

            count_vars = accumulate(cnf, neighbours)

            def get_count_var(k):
                if k <= 0: return None
                if k > len(count_vars): return None
                return count_vars[k-1]
            
            tile = grid_vars[row][column]
            ge_2 = get_count_var(2)
            ge_3 = get_count_var(3)
            ge_4 = get_count_var(4)

            # Alive rule: cell must have 2 or 3 neighbours
            if ge_2: cnf.append([-tile, ge_2])
            else: cnf.append([-tile])

            if ge_4: cnf.append([-tile, -ge_4])

            # Dead rule: cell must NOT have exactly 3 neighbours
            clause = [tile]
            if ge_3: clause.append(-ge_3)
            if ge_4: clause.append(ge_4)
            cnf.append(clause)
    
    for r in range(-1, n + 1):
        for c in range(-1, n + 1):

            if 0 <= r < n and 0 <= c < n: continue

            neighbours = []
            for d_row in [-1, 0, 1]:
                for d_column in [-1, 0, 1]:
                    if d_row == d_column == 0: continue
                    n_row = r + d_row
                    n_column = c + d_column
                    if 0 <= n_row < n and 0 <= n_column < n:
                        neighbours.append(grid_vars[n_row][n_column])
            
            if len(neighbours) < 3: continue

            count_vars = accumulate(cnf, neighbours)
            
            ge_3 = count_vars[2] 
            
            clause = [-ge_3]

            if len(count_vars) >= 4:
                ge_4 = count_vars[3] 
                clause.append(ge_4)
            
            cnf.append(clause)

    if target_pop > 0:
        all_cells = [grid_vars[r][c] for r in range(n) for c in range(n)]
        global_count_vars = accumulate(cnf, all_cells)

        if target_pop <= len(global_count_vars):
            cnf.append([global_count_vars[target_pop-1]])
        else:
            cnf.append([])
    return cnf, NEXT_VAR_ID-1, grid_vars

def accumulate(cnf, inputs):
    k = len(inputs)
    if k == 0:
        return []
    if k == 1:
        return [inputs[0]]

    registers = [[new_var() for j in range(k)] for i in range(k)]

    cnf.append([-inputs[0], registers[0][0]])
    cnf.append([-registers[0][0], inputs[0]])

    for j in range(1, k):
        cnf.append([-registers[0][j]])

    for i in range(1, k):
        x = inputs[i]
        for j in range(k):

            r = registers[i][j]

            if j < k:
                cnf.append([-registers[i-1][j], r])

            if j > 0:
                cnf.append([-registers[i-1][j-1], -x, r])
            
            if j == 0:
                cnf.append([-x, r])

            if j == 0:
                cnf.append([-r, registers[i-1][0], x])
            else:
                cnf.append([-r, registers[i-1][j], registers[i-1][j-1]])
                cnf.append([-r, registers[i-1][j], x])

    return registers[k-1]

def new_var():
    global NEXT_VAR_ID
    id = NEXT_VAR_ID
    NEXT_VAR_ID += 1
    return id

def call_solver(cnf, nr_vars, output_name, solver_name, verbosity):
    with open(output_name, "w") as file:
        file.write("p cnf " + str(nr_vars) + " " + str(len(cnf)) + '\n')
        for clause in cnf:
            file.write(' '.join(str(lit) for lit in clause) + ' 0\n')


    return subprocess.run(['./' + solver_name, '-model', '-verb=' + str(verbosity) , output_name], stdout=subprocess.PIPE)

def print_result(model, grid_vars):
    if model is None:
        print("UNSAT")
        return

    n = len(grid_vars)
    count = 0
    print(f"\nGrid Size: {n}x{n}")
    
    for r in range(n):
        row_str = ""
        for c in range(n):
            vid = grid_vars[r][c]
            if vid in model:
                row_str += "O "
                count += 1
            else:
                row_str += ". "
        print(row_str)
        
    print(f"Total Population: {count}")

def parse_model(result):
    if result.returncode != 10: # 10 = SAT, 20 = UNSAT
        return None
        
    output_str = result.stdout.decode('utf-8')
    model = set()
    for line in output_str.split('\n'):
        if line.startswith("v"):
            parts = line.split()
            for p in parts:
                if p != 'v':
                    val = int(p)
                    if val > 0: model.add(val)
    return model

def find_maximum(n, args):
    low = 0
    high = n*n
    best_model = None
    best_k = -1

    while low <= high:
        mid = (low + high) // 2
        print(f"Checking population >= {mid}...")

        cnf, num_var, grid_vars = encode(n, mid)

        result = call_solver(cnf, num_var, args.output, args.solver, args.verb)
        model = parse_model(result)

        if model:
            print("SAT.")
            best_model = model
            best_k = mid
            low = mid+1
        else:
            print("UNSAT.")
            high = mid - 1
    if best_model:
        print(f"\nMAXIMUM FOUND: {best_k}")
        print_result(best_model, grid_vars)
    else:
        print(f"\nNo solution found")


if __name__ == "__main__":
    parser = ArgumentParser()

    parser.add_argument("-n", "--input", default="8", type=str, help="Grid Size (N)")
    parser.add_argument("-o", "--output", default="formula.cnf", type=str, help="CNF Output file")
    parser.add_argument("-s", "--solver", default="glucose", type=str, help="Solver executable")
    parser.add_argument("-v", "--verb", default=0, type=int, choices=range(0,2), help="Verbosity")
    args = parser.parse_args()

    instance = load_instance(args.input)

    start_time = time.time()
    find_maximum(instance, args)
    duration = time.time() - start_time
    print(f"\nTotal excecution time: {duration:.4f} seconds")