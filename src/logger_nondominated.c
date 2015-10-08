#include <stdio.h>
#include <assert.h>

#include "coco.h"
#include "coco_archive.c"
#include "coco_archive.h"

#include "coco_utilities.c"
#include "coco_problem.c"
#include "coco_strdup.c"
#include "mo_pareto_filtering.c"

/* For making my multiobjective recorder work */

typedef struct {
    char *path;
    FILE *logfile;
    size_t max_size_of_archive;
    size_t number_of_evaluations;
} _logger_nondominated_t;

static struct coco_archive *mo_archive;
static struct coco_arhive_entry *entry;

static void private_logger_nondominated_evaluate_function(coco_problem_t *self, const double *x, double *y) {
  _logger_nondominated_t *data;
  size_t i;
  size_t j;
  size_t k;
  data = coco_get_transform_data(self);

  coco_evaluate_function(coco_get_transform_inner_problem(self), x, y);
  data->number_of_evaluations++;

  /* Open logfile if it is not already open */
  if (data->logfile == NULL) {
    data->logfile = fopen(data->path, "w");
    if (data->logfile == NULL) {
      char *buf;
      const char *error_format =
          "private_logger_nondominated_evaluate_function() failed to open log file '%s'.";
      size_t buffer_size = (size_t)snprintf(NULL, 0, error_format, data->path);
      buf = (char *)coco_allocate_memory(buffer_size);
      snprintf(buf, buffer_size, error_format, data->path);
      coco_error(buf);
      coco_free_memory(buf); /* Never reached */
    }
    fprintf(data->logfile, "# %lu variables  |  %lu objectives  |  func eval number\n",
            coco_get_number_of_variables(coco_get_transform_inner_problem(self)),
            coco_get_number_of_objectives(coco_get_transform_inner_problem(self)));
    
    /*********************************************************************/
    /* TODO: Temporary put it here, to check later */
    /* Allocate memory for the archive */
    mo_archive = (struct coco_archive *) malloc(1 * sizeof(struct coco_archive));
    coco_allocate_archive(mo_archive, data->max_size_of_archive,
                          coco_get_number_of_variables(coco_get_transform_inner_problem(self)),
                          coco_get_number_of_objectives(coco_get_transform_inner_problem(self)), 1);
    /*********************************************************************/
  }
  
  /********************************************************************************/
  /* Finish evaluations of 1 single solution of the pop, with nObj objectives,
   * now update the archive with this newly evaluated solution and check its nondomination. */
  coco_push_to_archive(&x, &y, mo_archive, 1, data->number_of_evaluations);
  mococo_pareto_filtering(mo_archive);  /***** TODO: IMPROVE THIS ROUTINE *****/
  coco_mark_updates(mo_archive, data->number_of_evaluations);
  
  /* Write out a line for this newly evaluated solution if it is nondominated */
  /* write main info to the log file for pfront*/
  for (i=0; i < mo_archive->update_size; i++) {
      entry = mo_archive->update[i];
      for (j=0; j < coco_get_number_of_variables(coco_get_transform_inner_problem(self)); j++) /* all decision variables of a solution */
          fprintf(data->logfile, "%13.10e\t", entry->var[j]);
      for (k=0; k < coco_get_number_of_objectives(coco_get_transform_inner_problem(self)); k++) /* all objective values of a solution */
          fprintf(data->logfile, "%13.10e\t", entry->obj[k]);
      fprintf(data->logfile, "%lu", entry->birth);  /* its timestamp (FEval) */
      fprintf(data->logfile, "\n");  /* go to the next line for another solution */
  }
  /********************************************************************************/
  
  /* Flush output so that impatient users can see progress. */
  fflush(data->logfile);
}

static void private_logger_nondominated_free_data(void *stuff) {
  _logger_nondominated_t *data;
  assert(stuff != NULL);
  data = stuff;

  if (data->path != NULL) {
    coco_free_memory(data->path);
    data->path = NULL;
  }
  /* if (data->target_values != NULL) {
    coco_free_memory(data->target_values);
    data->target_values = NULL;
  }
  */
  if (data->logfile != NULL) {
    fclose(data->logfile);
    data->logfile = NULL;
    
    /***************************************************************/
    /* TODO: Temporary put it here, to check later */
    coco_free_archive(mo_archive); /* free the archive */
    free(mo_archive);
    /***************************************************************/
  }
}

static coco_problem_t *logger_nondominated(coco_problem_t *inner_problem,
    const size_t max_size_of_archive, const char *path) {
  _logger_nondominated_t *data;
  coco_problem_t *self;

  data = coco_allocate_memory(sizeof(*data));
  data->number_of_evaluations = 0;
  data->path = coco_strdup(path);
  data->logfile = NULL; /* Open lazily in private_logger_nondominated_evaluate_function(). */
  data->max_size_of_archive = max_size_of_archive;
  self = coco_allocate_transformed_problem(inner_problem, data, private_logger_nondominated_free_data);
  self->evaluate_function = private_logger_nondominated_evaluate_function;
  return self;
}
