#!/usr/bin/env python3
r"""
Recursive Polynomial Coefficient Calculator - Version 2
Based on the Manuscript Method (Series "coefraíces")

This script implements the compact recursive sum-product formula to compute 
coefficients of a monic polynomial given its roots.

Formula:
  b_p = (-1)^p * \prod_{q=p}^{n-1} \sum_{i_q=n-q}^{r} a_{i_q}
  
Rule for upper limit 'r':
  - r = n if q = p
  - r = i_{q-1} - 1 if q > p

New in v2:
- Support for complex roots input via console.
- Automatic cleaning of numerical precision noise (residual imaginary parts).
- Dynamic symbolic formula generation with SymPy for any chosen degree n.
"""

import sys

def calculate_numeric_coefficients(roots):
    """
    Computes numerical values for the polynomial coefficients b_p from a list of roots.
    Supports complex and real numbers.
    
    Parameters:
    roots (list): Numeric values of the roots [a_1, a_2, ..., a_n].
    
    Returns:
    dict: Dictionary containing coefficient indices as keys and their values.
    """
    n = len(roots)
    coefficients = {n: 1.0 + 0j}  # b_n is always 1
    
    def compute_nested_sum(q, p, prev_i):
        # Determine the dynamic upper limit r
        r = n if q == p else prev_i - 1
        lower_limit = n - q
        
        # Pruning invalid branches where lower limit exceeds upper limit
        if lower_limit > r:
            return 0.0 + 0j
            
        # Innermost level of the nested summation
        if q == n - 1:
            total_sum = 0.0 + 0j
            for idx in range(lower_limit, r + 1):
                total_sum += roots[idx - 1]
            return total_sum
            
        # Recursive product of sum-product levels
        total_sum = 0.0 + 0j
        for idx in range(lower_limit, r + 1):
            current_val = roots[idx - 1]
            next_sum = compute_nested_sum(q + 1, p, idx)
            total_sum += current_val * next_sum
            
        return total_sum

    for p in range(n):
        val = compute_nested_sum(p, p, None)
        coefficients[p] = ((-1) ** (n - p)) * val
        
    # Clean numerical noise (e.g. imaginary parts like 1e-16j)
    cleaned_coeffs = {}
    for p, val in coefficients.items():
        # If the imaginary part is extremely small, convert to real
        if abs(val.imag) < 1e-11:
            cleaned_coeffs[p] = val.real
        else:
            cleaned_coeffs[p] = val
            
    return cleaned_coeffs


def generate_symbolic_formulas(n):
    """
    Generates symbolic formulas for a polynomial of degree n using SymPy.
    """
    try:
        import sympy as sp
        sym_roots = [sp.Symbol(f'a_{i}') for i in range(1, n + 1)]
        coefficients_sym = {n: sp.Integer(1)}
        
        def compute_nested_sum_sym(q, p, prev_i):
            r = n if q == p else prev_i - 1
            lower_limit = n - q
            
            if lower_limit > r:
                return sp.Integer(0)
                
            if q == n - 1:
                total_sum = sp.Integer(0)
                for idx in range(lower_limit, r + 1):
                    total_sum += sym_roots[idx - 1]
                return total_sum
                
            total_sum = sp.Integer(0)
            for idx in range(lower_limit, r + 1):
                current_val = sym_roots[idx - 1]
                next_sum = compute_nested_sum_sym(q + 1, p, idx)
                total_sum += current_val * next_sum
                
            return total_sum

        for p in range(n):
            val = compute_nested_sum_sym(p, p, None)
            coefficients_sym[p] = sp.simplify(((-1) ** (n - p)) * val)
            
        return coefficients_sym
    except ImportError:
        return None


def parse_root(s):
    """
    Parses a string representing a real or complex number.
    Handles 'i' as 'j' for user convenience.
    """
    s = s.strip().replace('i', 'j').replace(' ', '')
    if not s:
        return None
    try:
        # Check if it's purely real first to avoid converting to complex unnecessarily
        if 'j' not in s:
            try:
                return float(s)
            except ValueError:
                pass
        return complex(s)
    except ValueError:
        raise ValueError(f"No se pudo interpretar '{s}' como número real o complejo.")


def main():
    print("=" * 80)
    print(" CALCULADORA RECURSIVA DE COEFICIENTES POLINOMIALES (MÉTODO DEL MANUSCRITO v2)")
    print("=" * 80)
    print("Este script calcula los coeficientes b_p para un polinomio mónico dada sus raíces.")
    print("Soporta números reales y complejos (ej. 1+2i, -3, 2.5, -1-1j).\n")
    
    # Check if arguments are passed via command line
    if len(sys.argv) > 1:
        raw_input = ",".join(sys.argv[1:])
        print(f"Raíces recibidas por argumentos: {raw_input}")
    else:
        print("Ejemplos de entrada:")
        print("  - Raíces reales: 1, 2, 3")
        print("  - Raíces complejas conjugadas: 1+2i, 1-2i, 3, -2")
        print("  - Introduzca 'exit' para salir.\n")
        try:
            raw_input = input("Introduce las raíces separadas por comas: ")
        except (KeyboardInterrupt, EOFError):
            print("\nSaliendo...")
            return

    if raw_input.strip().lower() == 'exit':
        print("Saliendo...")
        return

    try:
        # Parse roots
        raw_roots = [r for r in raw_input.split(",") if r.strip()]
        roots = []
        for r in raw_roots:
            parsed = parse_root(r)
            if parsed is not None:
                roots.append(parsed)
                
        n = len(roots)
        if n == 0:
            print("Error: No se ingresaron raíces válidas.")
            return
            
        print(f"\nNúmero de raíces (n) = {n}")
        print("Raíces ingresadas:")
        for idx, r in enumerate(roots, start=1):
            if isinstance(r, complex):
                # Format complex numbers nicely (using 'i' instead of 'j')
                img_sign = "+" if r.imag >= 0 else "-"
                print(f"  a_{idx} = {r.real} {img_sign} {abs(r.imag)}i")
            else:
                print(f"  a_{idx} = {r}")
                
        # Calculate
        coeffs = calculate_numeric_coefficients(roots)
        
        print("\nCoeficientes calculados (b_p):")
        for p in sorted(coeffs.keys(), reverse=True):
            val = coeffs[p]
            if isinstance(val, complex):
                img_sign = "+" if val.imag >= 0 else "-"
                print(f"  b_{p} = {val.real:.6f} {img_sign} {abs(val.imag):.6f}i")
            else:
                print(f"  b_{p} = {val:.6f}")
                
        # Attempt symbolic formula generation
        print("\nGenerando fórmulas simbólicas de grado n = {}...".format(n))
        sym_coeffs = generate_symbolic_formulas(n)
        if sym_coeffs:
            print("\nFórmulas Algebraicas Simbólicas:")
            for p in sorted(sym_coeffs.keys(), reverse=True):
                formula_str = str(sym_coeffs[p]).replace('**', '^')
                print(f"  b_{p} = {formula_str}")
        else:
            print("SymPy no está instalado o no se pudo generar la expansión simbólica.")
            
    except Exception as e:
        print(f"\nError: {e}")
        
    print("=" * 80)


if __name__ == "__main__":
    main()
