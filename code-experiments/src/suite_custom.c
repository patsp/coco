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
                                  8, 9, 10, 11, 12, 13, 14, 15,
                                  16, 17, 18, 19, 20, 21, 22, 23,
                                  24, 25, 26, 27, 28, 29, 30, 31,
                                  32, 33, 34, 35, 36, 37, 38, 39,
                                  40, 41, 42, 43, 44, 45, 46, 47,
                                  48, 49, 50, 51, 52, 53, 54, 55,
                                  56, 57, 58, 59, 60 };

    suite = coco_suite_allocate("custom", 2, 60, dimensions,
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

/*
  The Thomson problem can be stated as
  (see https://en.wikipedia.org/wiki/Thomson_problem):

  Given M points, minimize sum_{1 <= i,j <= M with i<j} 1/r_{ij}
  subject to the M points being on the unit sphere,
  where r_{ij} = ||\mathrm{p}_i - \mathrm{p}_j|| and
  \mathrm{p}_i is the i-th point.
 */

/**
 * @brief Implements the Thomson problem's objective function
 * (posed as minimization) without connections to any COCO structures.
 */
static double f_thomson_raw(const double *x,
                            const size_t number_of_variables) {

  size_t i = 0;
  size_t j = 0;
  double result = 0.0;
  double x1 = 0.0;
  double y1 = 0.0;
  double z1 = 0.0;
  double x2 = 0.0;
  double y2 = 0.0;
  double z2 = 0.0;

  if (coco_vector_contains_nan(x, number_of_variables))
    return NAN;

  const int num_points = number_of_variables / 3;

  result = 0.0;
  for (i = 1; i < num_points; ++i) {
      x2 = x[3 * i];
      y2 = x[3 * i + 1];
      z2 = x[3 * i + 2];
      for (j = 0; j < i; ++j) {
          x1 = x[3 * j];
          y1 = x[3 * j + 1];
          z1 = x[3 * j + 2];
          result += 1 / sqrt((x1 - x2) * (x1 - x2) +
                             (y1 - y2) * (y1 - y2) +
                             (z1 - z2) * (z1 - z2));
      }
  }

  return result;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 */
static void f_thomson_evaluate(coco_problem_t *problem,
                                 const double *x, double *y) {
  assert(problem->number_of_objectives == 1);
  y[0] = f_thomson_raw(x, problem->number_of_variables);
  assert(y[0] + 1e-13 >= problem->best_value[0]);
}

/**
 * @brief Implements the Thomson problem's constraint
 * (all 3-dimensional points have to be on a unit sphere)
 * without connections to any COCO structures.
 */
static double f_thomson_constraint_raw(const double *x,
                                       const size_t number_of_variables,
                                       const int k) {

    int i = 0;
    double result = 0.0;
    double x1 = 0.0;
    double y1 = 0.0;
    double z1 = 0.0;
    double cons = 0.0;

    if (coco_vector_contains_nan(x, number_of_variables))
        return NAN;

    const int num_points = number_of_variables / 3;

    assert(0 <= k && k < num_points);

    result = 0.0;
    x1 = x[3 * k];
    y1 = x[3 * k + 1];
    z1 = x[3 * k + 2];
    cons = sqrt(x1 * x1 + y1 * y1 + z1 * z1) - 1.0;

    return cons;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 * Since the COCO framework deals with inequality constraints,
 * we use a hard-coded epsilon of 1e-8 for the equality
 * constraint threshold.
 */
static void f_thomson_evaluate_constraint(coco_problem_t *problem,
                                          const double *x, double *y) {
    int num_points = 0;
    int i = 0;
    double cons = 0.0;
    assert(problem->number_of_constraints ==
           2 * (problem->number_of_variables / 3));
    num_points = problem->number_of_variables / 3;
    for (i = 0; i < num_points; ++i) {
        cons = f_thomson_constraint_raw(x,
                                        problem->number_of_variables, i);
        y[2 * i] = cons - 1e-8;
        y[2 * i + 1] = -cons - 1e-8;
    }
}

/**
 * @brief Allocates the Thomson problem.
 */
static coco_problem_t *f_thomson_allocate(const size_t number_of_variables) {
    int i = 0;
    const int num_points = number_of_variables / 3;
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints = 2 * num_points;
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    /* TODO: Which seed should we use? */
    coco_random_state_t *random_generator = coco_random_new(1);
    double x = 0.0;
    double y = 0.0;
    double z = 0.0;
    double norm = 0.0;
    problem->evaluate_function = f_thomson_evaluate;
    problem->evaluate_constraint = f_thomson_evaluate_constraint;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        /* TODO: should we use different bounds? */
        problem->smallest_values_of_interest[i] = -1e3;
        problem->largest_values_of_interest[i] = 1e3;
        problem->best_parameter[i] = 0.0;
        problem->initial_solution[i] = 0.0;
    }
    /* Provide an initial solution with the points distributed
       on the sphere uniformly at random. */
    for (i = 0; i < num_points; ++i) {
        x = coco_random_normal(random_generator);
        y = coco_random_normal(random_generator);
        z = coco_random_normal(random_generator);
        norm = sqrt(x * x + y * y + z * z);
        if (norm != 0.0) {
            x /= norm;
            y /= norm;
            z /= norm;
        }

        problem->initial_solution[3 * i] = x;
        problem->initial_solution[3 * i + 1] = y;
        problem->initial_solution[3 * i + 2] = z;
    }

    /* The best known values are from: https://en.wikipedia.org/wiki/Thomson_problem#Configurations_of_smallest_known_energy */
    if (num_points == 2) {
        problem->best_value[0] = 0.500000000;
    } else if (num_points == 3) {
        problem->best_value[0] = 1.732050808;
    } else if (num_points == 4) {
        problem->best_value[0] = 3.674234614;
    } else if (num_points == 5) {
        problem->best_value[0] = 6.474691495;
    } else if (num_points == 6) {
        problem->best_value[0] = 9.985281374;
    } else if (num_points == 7) {
        problem->best_value[0] = 14.452977414;
    } else if (num_points == 8) {
        problem->best_value[0] = 19.675287861;
    } else if (num_points == 9) {
        problem->best_value[0] = 25.759986531;
    } else if (num_points == 10) {
        problem->best_value[0] = 32.716949460;
    } else if (num_points == 11) {
        problem->best_value[0] = 40.596450510;
    } else if (num_points == 12) {
        problem->best_value[0] = 49.165253058;
    } else if (num_points == 13) {
        problem->best_value[0] = 58.853230612;
    } else if (num_points == 14) {
        problem->best_value[0] = 69.306363297;
    } else if (num_points == 15) {
        problem->best_value[0] = 80.670244114;
    } else if (num_points == 16) {
        problem->best_value[0] = 92.911655302;
    } else if (num_points == 17) {
        problem->best_value[0] = 106.050404829;
    } else if (num_points == 18) {
        problem->best_value[0] = 120.084467447;
    } else if (num_points == 19) {
        problem->best_value[0] = 135.089467557;
    } else if (num_points == 20) {
        problem->best_value[0] = 150.881568334;
    } else {
        problem->best_value[0] = -1e8;
    }

    /* double-check feasibility of initial solution */
    assert(coco_is_feasible(problem, problem->initial_solution, NULL));

    coco_problem_set_id(problem, "thomson");

    coco_random_free(random_generator);

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

    if (function == 1) {
        problem = f_kleeminty_allocate(dimension);
    } else if (function == 2) {
        problem = f_thomson_allocate(dimension);
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

