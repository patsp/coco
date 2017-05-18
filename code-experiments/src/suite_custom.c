/**
 * @file  suite_custom.c
 * @brief Implementation of custom problems.
 */

#include "coco.h"

static coco_suite_t *coco_suite_allocate(const char *suite_name,
                                         const size_t number_of_functions,
                                         const size_t number_of_dimensions,
                                         const size_t *dimensions,
                                         const char *default_instances);

/**
 * @brief Sets the dimensions and default instances for the custom suite.
 */
static coco_suite_t *suite_custom_initialize(void) {

    coco_suite_t *suite;
    const size_t dimensions[] = { 1, 2, 3, 4, 5, 6, 7,
                                  8, 9, 10, 11, 12, 13, 14, 15 };

    suite = coco_suite_allocate("custom", 1, 15, dimensions,
                                "instances:1");

    return suite;
}

/*
  The constraints represent the Klee-Minty cube.
  Klee, V., Minty, G.J.:
  How good is the simplex algorithm? In: Shisha, O. (ed.) Inequalities III,
  pp. 159–175. Academic, New York (1972)

  The actual constraints are taken from
  https://en.wikipedia.org/wiki/Klee%E2%80%93Minty_cube.

  x_1              <= 5
  4x_1 +  x_2       <= 25
  8x_1 + 4x_2 + x_3 <= 125
  .
  .
  .
  2^Dx_1 + 2^(D-1)x_2 + ... + 4x_{D-1} + x_D <= 5^D
  x_1 >= 0, ..., x_D >= 0

  The objective is to maximize
  2^(D-1)x_1 + 2^(D-2)x_2 + ... + 2x_{D-1} + x_D.
*/

/**
 * @brief Implements the Klee-Minty objective function
 * without connections to any COCO structures.
 */
static double f_kleeminty_raw(const double *x,
                              const size_t number_of_variables) {

  size_t i = 0;
  double result;
  double factor;

  if (coco_vector_contains_nan(x, number_of_variables))
    return NAN;

  result = 0.0;
  factor = 1.0;
  for (i = 0; i < number_of_variables; ++i) {
      result += factor * x[number_of_variables - 1 - i];
      factor *= 2.0;
  }

  return -result;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 */
static void f_kleeminty_evaluate(coco_problem_t *problem,
                                 const double *x, double *y) {
  assert(problem->number_of_objectives == 1);
  y[0] = f_kleeminty_raw(x, problem->number_of_variables);
  assert(y[0] + 1e-13 >= problem->best_value[0]);
}

/**
 * @brief Implements the kth Klee-Minty constraint
 * without connections to any COCO structures.
 */
static double f_kleeminty_constraint_raw(const double *x,
                                         const size_t number_of_variables,
                                         const int k) {

    int i = 0;
    double result = 0.0;
    double factor = 0.0;
    double rhs = 0.0;

    assert(k <= number_of_variables);

    if (coco_vector_contains_nan(x, number_of_variables))
        return NAN;

    result = 0.0;
    factor = 1.0;
    rhs = 1.0;
    for (i = k - 1; i >= 0; --i) {
        if (i == k - 1) {
            result += x[i];
            factor = 4.0;
        } else {
            result += factor * x[i];
            factor *= 2.0;
        }
        rhs *= 5.0;
    }

    return result - rhs;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 */
static void f_kleeminty_evaluate_constraint(coco_problem_t *problem,
                                            const double *x, double *y) {
    size_t i = 0;
    assert(problem->number_of_constraints == problem->number_of_variables);
    for (i = 0; i < problem->number_of_constraints; ++i) {
        y[i] = f_kleeminty_constraint_raw(x,
                                          problem->number_of_variables,
                                          (int)(i + 1));
    }
}

/**
 * @brief Allocates the Klee-Minty problem.
 */
static coco_problem_t *f_kleeminty_allocate(const size_t number_of_variables) {
    int i = 0;
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints = number_of_variables;
    double powerOf5 = 1.0;
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    problem->evaluate_function = f_kleeminty_evaluate;
    problem->evaluate_constraint = f_kleeminty_evaluate_constraint;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        problem->smallest_values_of_interest[i] = 0.0;
        /* TODO: upper bound should be infinity,
           use large value instead for now. */
        problem->largest_values_of_interest[i] = 1e20;
        problem->best_parameter[i] = 0.0;
        problem->initial_solution[i] = 0.0;
        powerOf5 *= 5.0;
    }
    problem->best_parameter[number_of_variables - 1] = powerOf5;
    problem->best_value[0] = -powerOf5;

    coco_problem_set_id(problem, "kleeminty");

    return problem;
}

/**
 * @brief Returns the problem from the custom suite that
 *        corresponds to the given parameters.
 *
 * @param suite The COCO suite.
 * @param function_idx Index of the function (starting from 0).
 * @param dimension_idx Index of the dimension (starting from 0).
 * @param instance_idx Index of the instance (starting from 0).
 * @return The problem that corresponds to the given parameters.
 */
static coco_problem_t *suite_custom_get_problem(coco_suite_t *suite,
                                                const size_t function_idx,
                                                const size_t dimension_idx,
                                                const size_t instance_idx) {

    coco_problem_t *problem = NULL;

    const size_t function = suite->functions[function_idx];
    const size_t dimension = suite->dimensions[dimension_idx];
    const size_t instance = suite->instances[instance_idx];

    if (obj_function_type(function) == 1) {
        problem = f_kleeminty_allocate(dimension);
    } else {
        coco_error("get_cons_bbob_problem(): cannot retrieve problem f%lu instance %lu in %luD",
                   function, instance, dimension);
        return NULL; /* Never reached */
    }

    problem->suite_dep_function = function;
    problem->suite_dep_instance = instance;
    problem->suite_dep_index = coco_suite_encode_problem_index(suite, function_idx, dimension_idx, instance_idx);

    /* Use the standard stacked problem_id as problem_name and
     * construct a new suite-specific problem_id
     */
    coco_problem_set_name(problem, problem->problem_id);
    coco_problem_set_id(problem, "custom_f%02lu_i%02lu_d%02lu",
                        (unsigned long)function, (unsigned long)instance, (unsigned long)dimension);

    return problem;
}
