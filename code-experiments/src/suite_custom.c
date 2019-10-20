/**
 * @file  suite_custom.c
 * @brief Implementation of custom problems.
 */

#include "coco.h"

#include "cec2006_functions.c"

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
                                  56, 57, 58, 59, 60, 61, 62, 63,
                                  64, 65, 66, 67, 68, 69, 70, 71,
                                  72, 73, 74, 75, 76, 77, 78, 79,
                                  80, 81, 82, 83, 84, 85, 86, 87,
                                  88, 89, 90, 91, 92, 93, 94, 95,
                                  96, 97, 98, 99, 100 };

    suite = coco_suite_allocate("custom", 8, 100, dimensions,
                                "instances:1-15");

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
    size_t i = 0;
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

  This implementation assumes that all the points are given
  in one vector as follows:
  x = (x_1, y_1, z_1, x_2, y_2, z_2, ..., x_M, y_M, z_M)^T.
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
  const size_t num_points = number_of_variables / 3;

  if (coco_vector_contains_nan(x, number_of_variables))
    return NAN;

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
                                       const size_t k) {

    double x1 = 0.0;
    double y1 = 0.0;
    double z1 = 0.0;
    double cons = 0.0;

    if (coco_vector_contains_nan(x, number_of_variables))
        return NAN;

    assert(0 <= k && k < number_of_variables / 3);

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
    size_t num_points = 0;
    size_t i = 0;
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
static coco_problem_t *f_thomson_allocate(const size_t number_of_variables,
                                          const size_t function,
                                          const size_t instance) {
    size_t i = 0;
    const size_t num_points = number_of_variables / 3;
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints = 2 * num_points;
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    uint32_t rseed = (uint32_t)(function + 10000 * instance);
    coco_random_state_t *random_generator = coco_random_new(rseed);
    double x = 0.0;
    double y = 0.0;
    double z = 0.0;
    double norm = 0.0;
    problem->evaluate_function = f_thomson_evaluate;
    problem->evaluate_constraint = f_thomson_evaluate_constraint;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        /* Bounds are not relevant for this problem */
        problem->smallest_values_of_interest[i] = -5.0;
        problem->largest_values_of_interest[i] = 5.0;
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
    } else if (num_points == 21) {
        problem->best_value[0] = 167.641622399;
    } else if (num_points == 22) {
        problem->best_value[0] = 185.287536149;
    } else if (num_points == 23) {
        problem->best_value[0] = 203.930190663;
    } else if (num_points == 24) {
        problem->best_value[0] = 223.347074052;
    } else if (num_points == 25) {
        problem->best_value[0] = 243.812760299;
    } else if (num_points == 26) {
        problem->best_value[0] = 265.133326317;
    } else if (num_points == 27) {
        problem->best_value[0] = 287.302615033;
    } else if (num_points == 28) {
        problem->best_value[0] = 310.491542358;
    } else if (num_points == 29) {
        problem->best_value[0] = 334.634439920;
    } else if (num_points == 30) {
        problem->best_value[0] = 359.603945904;
    } else if (num_points == 31) {
        problem->best_value[0] = 385.530838063;
    } else if (num_points == 32) {
        problem->best_value[0] = 412.261274651;
    } else if (num_points == 33) {
        problem->best_value[0] = 440.204057448;
    } else if (num_points == 34) {
        problem->best_value[0] = 468.904853281;
    } else {
        problem->best_value[0] = -1e8;
    }

    /* double-check feasibility of initial solution */
    assert(coco_is_feasible(problem, problem->initial_solution, NULL));

    coco_problem_set_id(problem, "thomson");

    coco_random_free(random_generator);

    return problem;
}

/*
  A polygon optimization problem: Given a number of points,
  the goal is to move the points in a way such that the area
  of the polygon defined by the points is maximized
  while keeping the circumference fixed to a given value.

  More formally, the problem is stated as follows:
  Given K points in \mathbb{R}^2, the area of the polygon
  defined by K+1 nodes with the (K+1)-th node being
  w.l.o.g. (0, 0)^T, the goal is to maximize the area

  A(x) = (1/2) * \sum_{i=1}^{K-1}(x_i * x_{K+i+1} - x_{i+1} * x_{K+i})

  such that

  h(x) = \sqrt{x_1^2 + x_{K+1}^2} +
         \sum_{i=1}^{K} \sqrt{(x_i - x{i+1})^2 + (x_{K+i} - x_{K+i+1})^2}
         - L = 0.

  The function h(x) defines the circumference constraint, where
  L is the given circumference.

  This implementation assumes that all the points are given
  in one vector as follows:
  x = (x_1, x_2, x_K, ..., y_1, y_2, ..., y_K)^T,
  where here the (x_i, y_i)^T indicate coordinates in \mathbb{R}^2
  and above the x_i indicate vector elements of this vector defined
  here.

  Additionally, this implementation poses the problem as a minimization
  problem. The maximum area given the circumference can be computed,
  since in the limit case of infinitely many points, one gets a circle.
 */

static const double polygon_L = 10.0; /* hard-coded required circumference */

static double f_polygon_max_area(int num_points) {
    return ((polygon_L * polygon_L) /
            (4. * tan(coco_pi / (((double)num_points) + 1.0)))) *
        (1.0 / (((double)num_points) + 1.0));
}

/**
 * @brief Implements the polygon problem's objective function
 * (posed as minimization) without connections to any COCO structures.
 */
static double f_polygon_raw(const double *x,
                            const size_t number_of_variables) {

  int i = 0;
  double result = 0.0;
  const int num_points = (int)(number_of_variables / 2);

  if (coco_vector_contains_nan(x, number_of_variables))
    return NAN;

  result = 0.0;
  for (i = 0; i < num_points - 1; ++i) {
      result += x[i] * x[num_points + i + 1] - x[i + 1] * x[num_points + i];
  }

  return f_polygon_max_area(num_points) - 0.5 * result;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 */
static void f_polygon_evaluate(coco_problem_t *problem,
                                 const double *x, double *y) {
  assert(problem->number_of_objectives == 1);
  y[0] = f_polygon_raw(x, problem->number_of_variables);
  assert(y[0] + 1e-13 >= problem->best_value[0]);
}

/**
 * @brief Implements the polygon problem's constraint
 * without connections to any COCO structures.
 */
static double f_polygon_constraint_raw(const double *x,
                                       const size_t number_of_variables) {

    double result = 0.0;
    int i = 0;
    const int num_points = (int)(number_of_variables / 2);

    if (coco_vector_contains_nan(x, number_of_variables))
        return NAN;

    result += sqrt(x[0] * x[0] + x[num_points] * x[num_points]);
    result += sqrt(x[num_points - 1] * x[num_points - 1] +
                   x[2 * num_points - 1] * x[2 * num_points - 1]);
    for (i = 0; i < num_points - 1; ++i) {
        result += sqrt((x[i] - x[i + 1]) * (x[i] - x[i + 1]) +
                       (x[num_points + i] - x[num_points + i + 1]) *
                       (x[num_points + i] - x[num_points + i + 1]));
    }

    return result - polygon_L;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 * Since the COCO framework deals with inequality constraints,
 * we use a hard-coded epsilon of 1e-8 for the equality
 * constraint threshold.
 */
static void f_polygon_evaluate_constraint(coco_problem_t *problem,
                                          const double *x, double *y) {
    double cons = 0.0;
    assert(problem->number_of_constraints == 2);
    cons = f_polygon_constraint_raw(x, problem->number_of_variables);
    y[0] = cons - 1e-8;
    y[1] = -cons - 1e-8;
}

/**
 * @brief Allocates the polygon problem.
 */
static coco_problem_t *f_polygon_allocate(const size_t number_of_variables,
                                          const size_t function,
                                          const size_t instance) {
    int i = 0;
    int idx = 0;
    const int num_points = (int)(number_of_variables / 2);
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints = 2;
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    uint32_t rseed = (uint32_t)(function + 10000 * instance);
    coco_random_state_t *random_generator = coco_random_new(rseed);
    double x = 0.0;
    problem->evaluate_function = f_polygon_evaluate;
    problem->evaluate_constraint = f_polygon_evaluate_constraint;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        /* Bounds are not relevant for this problem */
        problem->smallest_values_of_interest[i] = -5.0;
        problem->largest_values_of_interest[i] = 5.0;
        problem->best_parameter[i] = 0.0;
        problem->initial_solution[i] = 0.0;
    }
    /* Provide an initial feasible solution.
       A trivial solution is constructed. All points
       except one with a random index are put to (0, 0)^T.
       The remaining one is put to (0, polygon_L / 2)^T.
    */
    x = coco_random_uniform(random_generator);
    idx = (int)(floor(x * num_points));
    assert(0 <= idx && idx < num_points);
    for (i = 0; i < num_points; ++i) {
        if (i != idx) {
            problem->initial_solution[i] = 0.0;
            problem->initial_solution[num_points + i] = 0.0;
        } else {
            problem->initial_solution[i] = 0.0;
            problem->initial_solution[num_points + i] = polygon_L / 2.0;
        }
    }

    problem->best_value[0] = 0.0;

    /* double-check feasibility of initial solution */
    assert(coco_is_feasible(problem, problem->initial_solution, NULL));

    coco_problem_set_id(problem, "polygon");

    coco_random_free(random_generator);

    return problem;
}

/**
 * @brief Implements the unconstrained polygon problem's objective function
 * (posed as minimization) without connections to any COCO structures.
 */
static double f_polygonunconstrained_raw(const double *x,
                                         const size_t number_of_variables) {

  int i = 0;
  double result = 0.0;
  const int num_points = (int)(number_of_variables / 2);
  const double constraint_violation =
      f_polygon_constraint_raw(x, number_of_variables);
  double *x_tmp = NULL;

  if (coco_vector_contains_nan(x, number_of_variables))
    return NAN;

  x_tmp = coco_duplicate_vector(x, number_of_variables);
  for (i = 0; i < number_of_variables; ++i) {
      x_tmp[i] = (x[i] / (constraint_violation + polygon_L)) * polygon_L;
  }
  result = 0.0;
  for (i = 0; i < num_points - 1; ++i) {
      result += x_tmp[i] * x_tmp[num_points + i + 1] -
          x_tmp[i + 1] * x_tmp[num_points + i];
  }
  coco_free_memory(x_tmp);

  return f_polygon_max_area(num_points) - 0.5 * result;
}

/**
 * @brief Uses the raw function to evaluate the COCO problem.
 */
static void f_polygonunconstrained_evaluate(coco_problem_t *problem,
                                            const double *x, double *y) {
  assert(problem->number_of_objectives == 1);
  y[0] = f_polygonunconstrained_raw(x, problem->number_of_variables);
  assert(y[0] + 1e-13 >= problem->best_value[0]);
}

/**
 * @brief Allocates the unconstrained polygon problem.
 */
static coco_problem_t *f_polygonunconstrained_allocate(const size_t
                                                       number_of_variables,
                                                       const size_t function,
                                                       const size_t instance) {
    int i = 0;
    int idx = 0;
    const int num_points = (int)(number_of_variables / 2);
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints = 0;
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    uint32_t rseed = (uint32_t)(function + 10000 * instance);
    coco_random_state_t *random_generator = coco_random_new(rseed);
    double x = 0.0;
    problem->evaluate_function = f_polygonunconstrained_evaluate;
    problem->evaluate_constraint = NULL;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        /* Bounds are not relevant for this problem */
        problem->smallest_values_of_interest[i] = -5.0;
        problem->largest_values_of_interest[i] = 5.0;
        problem->best_parameter[i] = 0.0;
        problem->initial_solution[i] = 0.0;
    }
    /* Provide an initial feasible solution.
       A trivial solution is constructed. All points
       except one with a random index are put to (0, 0)^T.
       The remaining one is put to (0, polygon_L / 2)^T.
    */
    x = coco_random_uniform(random_generator);
    idx = (int)(floor(x * num_points));
    assert(0 <= idx && idx < num_points);
    for (i = 0; i < num_points; ++i) {
        if (i != idx) {
            problem->initial_solution[i] = 0.0;
            problem->initial_solution[num_points + i] = 0.0;
        } else {
            problem->initial_solution[i] = 0.0;
            problem->initial_solution[num_points + i] = polygon_L / 2.0;
        }
    }

    problem->best_value[0] = 0.0;

    coco_problem_set_id(problem, "polygonunconstrained");

    coco_random_free(random_generator);

    return problem;
}

/* CEC 2006 */

typedef void (*cec2006_eval_fun_t)(double *x, double *f, double *g,
                                   double *h, int nx, int nf, int ng, int nh);

static cec2006_eval_fun_t get_cec2006_eval_fun(coco_problem_t *problem) {
    cec2006_eval_fun_t f = NULL;
    if (5 == problem->suite_dep_function) {
        f = cec2006_g03;
    } else if (6 == problem->suite_dep_function) {
        f = cec2006_g11;
    } else if (7 == problem->suite_dep_function) {
        f = cec2006_g13;
    } else if (8 == problem->suite_dep_function) {
        f = cec2006_g17;
    } else {
        assert(0);
    }
    return f;
}

static size_t
cec2006_get_num_equalityconstraints(const size_t function_index) {
    size_t num_equality_constraints = 0;
    if (5 == function_index) {
        num_equality_constraints = 1;
    } else if (6 == function_index) {
            num_equality_constraints = 1;
    } else if (7 == function_index) {
        num_equality_constraints = 3;
    } else if (8 == function_index) {
        num_equality_constraints = 4;
    } else {
        assert(0);
    }
    return num_equality_constraints;
}

static double cec2006_get_best_value(size_t function_index) {
    double best_value = 0.0;
    if (5 == function_index) {
        best_value = -1.0;
    } else if (6 == function_index) {
        best_value = 0.75;
    } else if (7 == function_index) {
        best_value = 0.0539498477624;
    } else if (8 == function_index) {
        best_value = 8853.53989187099;
    } else {
        assert(0);
    }
    return best_value;
}

static void initialize_cec2006_bounds(size_t function_index,
                                      double *smallest_values_of_interest,
                                      double *largest_values_of_interest,
                                      size_t number_of_variables) {
    int i = 0;
    if (5 == function_index) {
        if (10 == number_of_variables) {
            for (i = 0; i < number_of_variables; ++i) {
                smallest_values_of_interest[i] = 0.0;
                largest_values_of_interest[i] = 1.0;
            }
        }
    } else if (6 == function_index) {
        if (2 == number_of_variables) {
            for (i = 0; i < number_of_variables; ++i) {
                smallest_values_of_interest[i] = -1.0;
                largest_values_of_interest[i] = 1.0;
            }
        }
    } else if (7 == function_index) {
        if (5 == number_of_variables) {
            smallest_values_of_interest[0] = -2.3;
            largest_values_of_interest[0] = 2.3;
            smallest_values_of_interest[1] = -2.3;
            largest_values_of_interest[1] = 2.3;
            smallest_values_of_interest[2] = -3.2;
            largest_values_of_interest[2] = 3.2;
            smallest_values_of_interest[3] = -3.2;
            largest_values_of_interest[3] = 3.2;
            smallest_values_of_interest[4] = -3.2;
            largest_values_of_interest[4] = 3.2;
        }
    } else if (8 == function_index) {
        if (6 == number_of_variables) {
            smallest_values_of_interest[0] = 0.0;
            largest_values_of_interest[0] = 400.0;
            smallest_values_of_interest[1] = 0.0;
            largest_values_of_interest[1] = 1000.0;
            smallest_values_of_interest[2] = 340.0;
            largest_values_of_interest[2] = 420.0;
            smallest_values_of_interest[3] = 340.0;
            largest_values_of_interest[3] = 420.0;
            smallest_values_of_interest[4] = -1000.0;
            largest_values_of_interest[4] = 1000.0;
            smallest_values_of_interest[5] = 0.0;
            largest_values_of_interest[5] = 0.5236;
        }
    } else {
        assert(0);
    }
}

/**
 * @brief Evaluates a CEC2006 problem's objective and
 * equality constraint function.
 */
static void f_cec2006_evaluate_helper(coco_problem_t *problem,
                                      const double *x,
                                      double *f, double *h) {
    cec2006_eval_fun_t eval_fun = get_cec2006_eval_fun(problem);
    assert(eval_fun != NULL);

    assert(x != NULL);
    assert(f != NULL);
    assert(h != NULL);

    eval_fun((double *)x, f, NULL, h,
             (int)problem->number_of_variables,
             (int)problem->number_of_objectives,
             0,
             (int)problem->number_of_constraints);
}

/**
 * @brief Evaluates a CEC2006 problem's objective function.
 */
static void f_cec2006_evaluate(coco_problem_t *problem,
                               const double *x, double *y) {
    double *h_tmp = NULL;

    assert(problem->number_of_objectives == 1);
    /* problem->number_of_constraints contains 2 * "number
       of equality constraints" */
    h_tmp = coco_allocate_vector(problem->number_of_constraints / 2);
    assert(h_tmp != NULL);
    f_cec2006_evaluate_helper(problem, x, y, h_tmp);
    coco_free_memory(h_tmp);
    assert(y[0] + 1e-13 >= problem->best_value[0]);
}

/**
 * @brief Evaluates a CEC2006 problem's equality constraint function.
 * Since the COCO framework deals with inequality constraints,
 * we use a hard-coded epsilon of 1e-8 for the equality
 * constraint threshold.
 */
static void f_cec2006_evaluate_constraint(coco_problem_t *problem,
                                          const double *x, double *y) {
    size_t i = 0;
    double f_tmp = 0.0;
    double *h_tmp = NULL;

    assert(problem->number_of_objectives == 1);

    /* problem->number_of_constraints contains 2 * "number
       of equality constraints" */
    h_tmp = coco_allocate_vector(problem->number_of_constraints / 2);
    assert(h_tmp != NULL);

    f_cec2006_evaluate_helper(problem, x, &f_tmp, h_tmp);

    for (i = 0; i < problem->number_of_constraints / 2; ++i) {
        y[2 * i] = h_tmp[i] - 1e-8;
        y[2 * i + 1] = -h_tmp[i] - 1e-8;
    }

    coco_free_memory(h_tmp);
}

/**
 * @brief Allocates a CEC 2006 problem.
 */
static coco_problem_t *f_cec2006_allocate(const size_t number_of_variables,
                                          const size_t function,
                                          const size_t instance) {
    size_t i = 0;
    const size_t number_of_objectives = 1;
    const size_t number_of_constraints =
        2 * cec2006_get_num_equalityconstraints(function);
    coco_problem_t *problem = coco_problem_allocate(number_of_variables,
                                                    number_of_objectives,
                                                    number_of_constraints);
    uint32_t rseed = (uint32_t)(function + 10000 * instance);
    coco_random_state_t *random_generator = coco_random_new(rseed);
    problem->evaluate_function = f_cec2006_evaluate;
    problem->evaluate_constraint = f_cec2006_evaluate_constraint;
    problem->initial_solution = coco_allocate_vector(number_of_variables);
    for (i = 0; i < number_of_variables; ++i) {
        problem->smallest_values_of_interest[i] = 0.0;
        problem->largest_values_of_interest[i] = 0.0;
        /* TODO: Is the best_parameter important to set? */
        problem->best_parameter[i] = 0.0;
        /* TODO: Can we provide a feasible initial solution?
           Just provide zeros vector for now. */
        problem->initial_solution[i] = 0.0;
    }
    /* double-check feasibility of initial solution */
    /* assert(coco_is_feasible(problem, problem->initial_solution, NULL)); */

    initialize_cec2006_bounds(function,
                              problem->smallest_values_of_interest,
                              problem->largest_values_of_interest,
                              number_of_variables);

    problem->best_value[0] = cec2006_get_best_value(function);

    coco_problem_set_id(problem, "CEC2006");

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
        problem = f_thomson_allocate(dimension, function, instance);
    } else if (function == 3) {
        problem = f_polygon_allocate(dimension, function, instance);
    } else if (function == 4) {
        problem = f_polygonunconstrained_allocate(dimension, function,
                                                  instance);
    } else if (5 <= function && function <= 8) {
        problem = f_cec2006_allocate(dimension, function, instance);
    } else {
        coco_error("get_custom_problem(): "
                   "cannot retrieve problem f%lu instance %lu in %luD",
                   function, instance, dimension);
        return NULL; /* Never reached */
    }

    problem->suite_dep_function = function;
    problem->suite_dep_instance = instance;
    problem->suite_dep_index =
        coco_suite_encode_problem_index(suite, function_idx,
                                        dimension_idx, instance_idx);

    /* Use the standard stacked problem_id as problem_name and
     * construct a new suite-specific problem_id
     */
    coco_problem_set_name(problem, problem->problem_id);
    coco_problem_set_id(problem, "custom_f%02lu_i%02lu_d%02lu",
                        (unsigned long)function, (unsigned long)instance,
                        (unsigned long)dimension);

    return problem;
}

