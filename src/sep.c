/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the Common Development
 * and Distribution License (the "License").  You may not use this file except
 * in compliance with the License.
 *
 * You can obtain a copy of the license at src/PLAN.LICENSE.  See the License
 * for the specific language governing permissions and limitations under the
 * License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each file and
 * include the License file at src/PLAN.LICENSE.  If applicable, add the
 * following below this CDDL HEADER, with the fields enclosed by brackets "[]"
 * replaced with your own identifying information:
 * Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */

/*
 * Copyright (c) 2011, Nick Zivkovic. All rights reserved.
 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>

/*
 * Currently the maximum number of points is 100.
 */
#define	MAX_PTS	100

/*
 * The basic algoritms works like this. We have a graph G(V, E). Each node
 * represents a point (aka X-Y coordinate pair) on the first quadrant of a
 * cartesian plane. We initialize the graph such that every point is connected
 * to every other point (essentially a complete digraph). Whenever a line comes
 * between two points, we disconnect them in the graph (if they're still
 * connected).
 *
 * This is an instance of a minimal set cover algorithm. We want, with minimal
 * number of axis-parallel lines, to separate as many points as possible. We do
 * this by repeatedly disconnecting the largest subsets of points until we have
 * no other connections.
 *
 * Because this is a complete digraph, we have (n*(n-1)) connections, where `n`
 * is the number of points.
 *
 * From the start, we know that the largest subset of pairs separable by a
 * single line is exactly half of the points (if we have an even number of
 * points) such that only a fraction of the connections remain (except in the
 * case of 2 points, where the remaining is 0).
 *
 * Our algorithms always assumes that the maximum separations occur within a
 * range if we draw a line in the middle of the range. Ranges aren't
 * coordinates, but rather integral positions of points along the x and y axis
 * (we store pointers to point structures, sorted by x or y coordinate).
 *
 * If we were restricted to only one axis, it would _always_ be true that
 * halfing a range splits the greatest number of points. However, as we have to
 * deal with two axese, we could very well have no connections in our specified
 * range. This is why, before we split the range in half with a line, we check
 * to see if there are connections between points on either side of the line.
 * If so, we split the range in half.
 *
 * For each axis, we add our lines in a heap-like order, by splitting the axis
 * in half, and then recursively splitting the halves in half.
 *
 * We precompute all of the lines, but don't actually disconnect any points in
 * the graph.
 *
 * We then walk the heaps (we have 1 heap for horizontal lines, and 1 heap for
 * vertical lines), in alternating order (X, Y, X, Y, X, ...), checking for
 * connections. If we find connections (as stated above), we "commit" the line,
 * disconnect the points that are no longer reachable from each other, and move
 * to the next one. If not, we silently move on to the next line that would
 * work.
 *
 * We keep doing this until the graph has no connections left.
 *
 * This will usually yield a solution that is better than the worst case
 * ((number-of-points)-1 lines)), but not necessarily the best case. Such is
 * the nature of greedy algorithms.
 */

typedef struct point point_t;
typedef struct line line_t;

typedef enum axis {
	X,
	Y
} axis_t;

typedef enum bias {
	RIGHT,
	LEFT,
	TOP,
	BOTTOM,
} bias_t;

typedef enum ret_val {
	SUCCESS,
	READ_NO_POINTS,
	READ_N_POINTS_MORE_LESS,
	READ_NOT_FOUND,
	INS_LN_EXIST,
} ret_val_t;




/*
 * Even though we store our lines in binary trees, we use this structure and an
 * array to track the exact order in which we added the lines.
 */
struct line {
	int		ln_axis;
	int		ln_committed;
	float		ln_inter;
};


struct point {
	int		pt_x;
	int		pt_y;
	int		pt_con_cnt;	/* the num of pts this pt is con to */
	int		pt_self_ix;
	point_t		**pt_connections;
	/*
	 * A point can at most have 4 adjacent lines 2x + 2y.
	 */
	line_t		*pt_adj_ln_x1;
	line_t		*pt_adj_ln_x2;
	line_t		*pt_adj_ln_y1;
	line_t		*pt_adj_ln_y2;
};

/*
 * A multidimentional array consisting of pointers to point_t's, so that we can
 * get the point data structures in O(1) time.
 * XXX: Currently not used. Maybe later.
 */
/* point_t *point_ref[MAX_PTS][MAX_PTS]; */

/*
 * The memory-area where all of our point structs are stored. They are all
 * sorted by x-coordinate.
 */
static point_t points[MAX_PTS];

/*
 * These are arrays of pointers to the point structs. In the first one, the
 * points are separated by x cooridinate, and in the second one they are
 * separated by y coordinate. Really, only the second one is necessary, if our
 * input is pre sorted by X-Coordinate, however, having both makes this code
 * adaptable to random inputs.
 */
static point_t *sorted_x_pt[MAX_PTS];
static point_t *sorted_y_pt[MAX_PTS];
/* these two could be used in an implementation where y or x coords overlap */
static int x_pt_taken[MAX_PTS];
static int y_pt_taken[MAX_PTS];

/*
 * need at most MAX_PTS lines to separate MAX_PTS points
 * This is essentially the set S, as described in the HW.
 *
 * We keep the x_lines separated from the y_lines. However, we store pointers
 * to ALL of the lines in all_lines, in the order that the lines were found.
 */
static line_t x_lines[MAX_PTS];
static line_t y_lines[MAX_PTS];
static line_t *all_lines[MAX_PTS];

// int x_next_avail = 0;
// int y_next_avail = 0;

static int n_x_lines = 0;
static int n_y_lines = 0;
static int n_lines = 0;
static int n_pts = 0;
static int rem_cons = 0;

/*
 * These variables represent the number of points that have unique X and unique
 * Y coordinates. In the homework, these are useless, because all points are
 * supposed to never have overlapping x or y coordinates. But I want my
 * solution to be efficient in the general case.
 */
// int uniq_x = 0;
// int uniq_y = 0;




/*
 * The comparison functions used by quicksort.
 */
static int
x_pt_compare(const void *ptr1, const void *ptr2)
{
	point_t **p1 = (point_t **)ptr1;
	point_t **p2 = (point_t **)ptr2;

	if ((*p1)->pt_x > (*p2)->pt_x) {
		return (1);
	}

	if ((*p1)->pt_x < (*p2)->pt_x) {
		return (-1);
	}

	return (0);

}

static int
y_pt_compare(const void *ptr1, const void *ptr2)
{
	point_t **p1 = (point_t **)ptr1;
	point_t **p2 = (point_t **)ptr2;

	if ((*p1)->pt_y > (*p2)->pt_y) {
		return (1);
	}

	if ((*p1)->pt_y < (*p2)->pt_y) {
		return (-1);
	}

	return (0);
}


static void
sort_points()
{

	qsort(sorted_x_pt, n_pts, sizeof (point_t *),
		&x_pt_compare);

	qsort(sorted_y_pt, n_pts, sizeof (point_t *),
		&y_pt_compare);

}





/*
 * We create and initialize the arrays of pointers that store the
 * connectednesses of the graphs.
 */
static void
initialize_connections()
{
	int i = 0;
	while (i < n_pts) {
		points[i].pt_connections = malloc(sizeof (point_t *)*MAX_PTS);
		i++;
	}
	i = 0;
	int j = 0;
	while (i < n_pts) {
		j = 0;
		points[i].pt_self_ix = i;
		while (j < n_pts) {
			if (i != j) {
				points[i].pt_connections[j] = &(points[j]);
				points[i].pt_con_cnt++;
				rem_cons++;
			} else {
				points[i].pt_connections[j] = NULL;
			}
			j++;
		}
		i++;
	}
	if (rem_cons != (n_pts*(n_pts-1))) {
		(void) printf("rem_cons=%d, but should be %d\n", rem_cons,
			    (n_pts*(n_pts-1)));
		exit(0);
	}

}

static void
free_connections()
{
	int i = 0;
	while (i < n_pts) {
		free(points[i].pt_connections);
		i++;
	}
	n_pts = 0;
	n_lines = 0;
	n_x_lines = 0;
	n_y_lines = 0;
}

static void
print_connections()
{
	int i = 0;
	int j = 0;
	while (i < n_pts) {
		(void) printf("%d: [ ", i);
		j = 0;
		while (j < n_pts) {
			(void) printf("%8p ",
				(void*) points[i].pt_connections[j]);
			j++;
		}
		(void) printf("]\n");
		i++;
	}
}


static int
read_instance_file(int n)
{
	/* most file systems don't support file-names larger than 255 bytes */
	char str[255];
	char *s = &str[0];
	(void) sprintf(s, "instance%.2d", n);
	FILE *inst = fopen(s, "r");

	if (inst == NULL) {
		return (READ_NOT_FOUND);
	}

	int ret = fscanf(inst, "%d", &n_pts);
	int x = 0;
	int y = 0;
	int i = 0;

	if (ret == EOF) {
		return (READ_NO_POINTS);
	}

	while (i < MAX_PTS) {
		x_pt_taken[i] = 0;
		y_pt_taken[i] = 0;
		i++;
	}

	i = 0;

	while (fscanf(inst, "%d %d", &x, &y) != EOF && i < MAX_PTS) {
		points[i].pt_x = x;
		x_pt_taken[x] = 1;
		points[i].pt_y = y;
		y_pt_taken[i] = 1;
		points[i].pt_con_cnt = 0;
		points[i].pt_adj_ln_x1 = NULL;
		points[i].pt_adj_ln_y1 = NULL;
		points[i].pt_adj_ln_x2 = NULL;
		points[i].pt_adj_ln_y2 = NULL;
		i++;
	}

	if (i != n_pts) {
		return (READ_N_POINTS_MORE_LESS);
	}

	/*
	 * Make the pointers in the pre-sorted arrays point to data.
	 */
	int j = 0;
	while (j < n_pts) {
		sorted_x_pt[j] = &(points[j]);
		sorted_y_pt[j] = &(points[j]);
		j++;
	}

	return (SUCCESS);
}

/*
 * We serialize the solution here. We also free all previously used memory.
 */
static void
serialize_solution(int n)
{

	/* most file systems don't support file-names larger than 255 bytes */
	char str[255];
	char *s = &str[0];
	(void) sprintf(s, "greedy_solution_%.2d", n);
	FILE *out = fopen(s, "w");
	int i = 0;
	(void) fprintf(out, "%d\n", (n_lines));
	while (i < n_lines) {
		switch (all_lines[i]->ln_axis) {

		case X:
			(void) fprintf(out, "v ");
			break;

		case Y:
			(void) fprintf(out, "h ");
			break;
		}
		(void) fprintf(out, "%f\n", all_lines[i]->ln_inter);
		i++;
	}
	(void) fclose(out);

}

/*
 * get_point_nearest_inter will return the index of the point that is closes to
 * the left side of the specified intersect. Takes at most O(n) time. If we
 * return -1, then there is no point to the left of the intersect/line.
 * The index returned is the index of the point within the sorted arrays.
 */
static int
get_point_nearest_inter(int axis, float inter)
{
	point_t **ls;
	if (axis == X) {
		ls = sorted_x_pt;
	} else {
		ls = sorted_y_pt;
	}

	int i = 0;
	float coord = 0;
	while (i < n_pts) {

		if (axis == X) {
			coord = (float)ls[i]->pt_x;
		} else {
			coord = (float)ls[i]->pt_y;
		}


		if ((float)coord > inter) {
			return ((i-1));
		}

		i++;
	}

	return (-1);
}

static void
disconnect_points(int pt1, int pt2)
{

		if ((points[pt1]).pt_connections[pt2] != NULL) {
			(points[pt1]).pt_connections[pt2] = NULL;
			(points[pt2]).pt_connections[pt1] = NULL;
			(points[pt1]).pt_con_cnt--;
			(points[pt2]).pt_con_cnt--;
			rem_cons -= 2;
		}
}

static void
commit(line_t *l)
{
	l->ln_committed = 1;
	point_t **ls;
	int axis = l->ln_axis;
	float inter = (float)l->ln_inter;
	all_lines[n_lines] = l;
	int p = get_point_nearest_inter(axis, inter);
	if (axis == X) {
		ls = sorted_x_pt;
	} else {
		ls = sorted_y_pt;
	}
	int i = 0;
	int j = p;
	while (i <= p) {
		j = p+1;
		while (j < n_pts) {
			disconnect_points(ls[i]->pt_self_ix,
				ls[j]->pt_self_ix);
			j++;
		}
		i++;
	}
	n_lines++;
}

static void
print_pts_by_axis(int axis)
{
	point_t **ls;
	if (axis == X) {
		ls = sorted_x_pt;
		(void) printf("Points By X-Coord\n");
	} else {
		ls = sorted_y_pt;
		(void) printf("Points By Y-Coord\n");
	}

	int i = 0;
	while (i < n_pts) {
		(void) printf("[%d](%d, %d)\n", i, ls[i]->pt_x, ls[i]->pt_y);
		i++;
	}
}

/*
 * Div adds a line between points points[from] and points[to]. However,
 * div_axis() does _not_ disconnect anything. All it does is split the
 * specified axis in half repeatedly, and stores the lines in the order in
 * which they are added.
 */
static void
div_axis(int axis, int from, int to)
{
	if (from == to) {
		return;
	}

	int span;
	int half;
	float pta;
	float ptb;
	point_t *pt1;
	point_t *pt2;
	float ptdiff;
	float ptmid_dist;
	float ptmid_coord;
	line_t *cur_ln;
	point_t **ls;
	if (axis == X) {
		ls = &(sorted_x_pt[0]);
		span = to - from;
		if (span == 0 || span == 1) {
			return;
		}

		if (span%2) {
			half = ((span-1)/2);
		} else {
			half = span/2;
		}

		if (half) {
			pt1 = (ls[(from + (half))]);
			pt2 = (ls[(from + (half+1))]);
			pta = (float)pt1->pt_x;
			ptb = (float)pt2->pt_x;
			ptdiff = ptb - pta;
			ptmid_dist = ptdiff/2;
			ptmid_coord = pta + ptmid_dist;
			cur_ln = &(x_lines[n_x_lines]);
			cur_ln->ln_axis = X;
			cur_ln->ln_inter = ptmid_coord;
			cur_ln->ln_committed = 0;
			n_x_lines++;
			if (span != 2) {
				div_axis(axis, from, (from+half));
				div_axis(axis, (from+half), to);
			}
		}
		return;
	} else {
		ls = &(sorted_y_pt[0]);
		span = to - from;
		if (span == 0 || span == 1) {
			return;
		}

		/* below conditional can be rewritten as ((span-(span%2))/2) */
		if (span%2) {
			half = ((span-1)/2);
		} else {
			half = span/2;
		}

		/* when half is zero, we can't half this span */
		if (half) {
			pt1 = ls[(from + (half))];
			pt2 = ls[(from + (half+1))];
			pta = (float)pt1->pt_y;
			ptb = (float)pt2->pt_y;
			ptdiff = ptb - pta;
			ptmid_dist = ptdiff/2;
			ptmid_coord = pta + ptmid_dist;
			cur_ln = &(y_lines[n_y_lines]);
			cur_ln->ln_axis = Y;
			cur_ln->ln_inter = ptmid_coord;
			cur_ln->ln_committed = 0;
			n_y_lines++;
			if (span != 2) {
				div_axis(axis, from, (from+half));
				div_axis(axis, (from+half), to);
			}
		}
		return;
	}
}

/*
 * check_con returns true if any of the on the left of line ln have any
 * connections to any of the points on the right of line ln.
 */
static int
check_con(line_t *ln)
{
	int axis = ln->ln_axis;
	float inter = ln->ln_inter;
	int p = get_point_nearest_inter(axis, inter);
	point_t **ls;

	if (axis == X) {
		ls = &(sorted_x_pt[0]);
	} else {
		ls = &(sorted_y_pt[0]);
	}

	int i = 0;
	int j = p+1;
	while (i < (p+1)) {
		j = p+1;
		while (j < n_pts) {
			if ((points[(ls[i]->pt_self_ix)].
				pt_connections[(ls[j]->pt_self_ix)]) != NULL) {
				return (1);
			}
			j++;
		}
	i++;
	}
	return (0);
}

/*
 * Initialize all required data to zero (or some other default value).
 * Allocate required space where needed.
 */
static void
init_data()
{

	/* ok maybe not */
	// int i = 0;

}

#define	READ_N_POINTS_ERR "The file %d has more|less points than it should\n"
#define	READ_NO_INS_ERR "No instance file [%d] found\n"
#define	READ_NO_POINTS_ERR "There are no points in file %d\n"
#define	READ_ONLY_HEAD "Only the header value was found\n"
int
main()
{
	int instance_number = 1;
	while (instance_number < 100) {
		init_data();

		int file_status = read_instance_file(instance_number);

		switch (file_status) {

		case READ_NOT_FOUND:
			(void) fprintf(stderr, READ_NO_INS_ERR,
				instance_number);
			(void) fprintf(stderr, "Quitting\n");
			exit(0);
			break;

		case READ_N_POINTS_MORE_LESS:
			(void) fprintf(stderr, READ_N_POINTS_ERR,
				instance_number);
			(void) fprintf(stderr, "Quitting\n");
			exit(0);
			break;

		case READ_NO_POINTS:
			(void) fprintf(stderr, READ_NO_POINTS_ERR,
				instance_number);
			(void) fprintf(stderr, READ_ONLY_HEAD);
			(void) fprintf(stderr, "Quitting\n");
			exit(0);
			break;
		}

		sort_points();
		initialize_connections();



		div_axis(X, 0, (n_pts-1));
		div_axis(Y, 0, (n_pts-1));


		int clx = 0;
		int cly = 0;
		int con = 0;
		while (rem_cons && clx < n_x_lines && cly < n_y_lines) {
			con = check_con(&(x_lines[clx]));
			if (con) {
				commit(&(x_lines[clx]));
			}
			clx++;

			con = check_con(&(y_lines[cly]));
			if (con) {
				commit(&(y_lines[cly]));
			}
			cly++;
		}

		serialize_solution(instance_number);
		(void) printf("Solved instance %.2d\n", instance_number);
		free_connections();
		instance_number++;

	}

}
