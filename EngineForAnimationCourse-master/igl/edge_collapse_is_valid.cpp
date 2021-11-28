// This file is part of libigl, a simple c++ geometry processing library.
// 
// Copyright (C) 2015 Alec Jacobson <alecjacobson@gmail.com>
// 
// This Source Code Form is subject to the terms of the Mozilla Public License 
// v. 2.0. If a copy of the MPL was not distributed with this file, You can 
// obtain one at http://mozilla.org/MPL/2.0/.
#include "edge_collapse_is_valid.h"
#include "collapse_edge.h"
#include "circulation.h"
#include "intersect.h"
#include "unique.h"
#include "list_to_matrix.h"
#include <vector>

IGL_INLINE bool igl::edge_collapse_is_valid(
    const int e,
    const Eigen::MatrixXi& F,
    const Eigen::MatrixXi& E,
    const Eigen::VectorXi& EMAP,
    const Eigen::MatrixXi& EF,
    const Eigen::MatrixXi& EI)
{
    using namespace Eigen;
    using namespace std;
    // For consistency with collapse_edge.cpp, let's determine edge flipness
    // (though not needed to check validity)
    const int eflip = E(e, 0) > E(e, 1);
    // source and destination
    const int s = eflip ? E(e, 1) : E(e, 0);
    const int d = eflip ? E(e, 0) : E(e, 1);

    if (s == IGL_COLLAPSE_EDGE_NULL && d == IGL_COLLAPSE_EDGE_NULL)
    {
        return false;
    }
    // check if edge collapse is valid: intersection of vertex neighbors of s and
    // d should be exactly 2+(s,d) = 4
    // http://stackoverflow.com/a/27049418/148668
    {
        // all vertex neighbors around edge, including the two vertices of the edge
        const auto neighbors = [](
            const int e,
            const bool ccw,
            const Eigen::MatrixXi& F,
            const Eigen::MatrixXi& E,
            const Eigen::VectorXi& EMAP,
            const Eigen::MatrixXi& EF,
            const Eigen::MatrixXi& EI)
        {
            vector<int> N, uN;
            vector<int> V2Fe = circulation(e, ccw, EMAP, EF, EI);
            for (auto f : V2Fe)
            {
                N.push_back(F(f, 0));
                N.push_back(F(f, 1));
                N.push_back(F(f, 2));
            }
            vector<size_t> _1, _2;
            igl::unique(N, uN, _1, _2);
            VectorXi uNm;
            list_to_matrix(uN, uNm);
            return uNm;
        };
        VectorXi Ns = neighbors(e, eflip, F, E, EMAP, EF, EI);
        VectorXi Nd = neighbors(e, !eflip, F, E, EMAP, EF, EI);
        VectorXi Nint = igl::intersect(Ns, Nd);
        if (Nint.size() != 4)
        {
            return false;
        }
        if (Ns.size() == 4 && Nd.size() == 4)
        {
            VectorXi NsNd(8);
            NsNd << Ns, Nd;
            VectorXi Nun, _1, _2;
            igl::unique(NsNd, Nun, _1, _2);
            // single tet, don't collapse
            if (Nun.size() == 4)
            {
                return false;
            }
        }// This file is part of libigl, a simple c++ geometry processing library.
// 
// Copyright (C) 2015 Alec Jacobson <alecjacobson@gmail.com>
// 
// This Source Code Form is subject to the terms of the Mozilla Public License 
// v. 2.0. If a copy of the MPL was not distributed with this file, You can 
// obtain one at http://mozilla.org/MPL/2.0/.
#ifndef IGL_EDGE_COLLAPSE_IS_VALID_H
#define IGL_EDGE_COLLAPSE_IS_VALID_H
#include "igl_inline.h"
#include <Eigen/Core>
#include <vector>
        namespace igl
        {
            // Assumes (V,F) is a closed manifold mesh (except for previouslly collapsed
            // faces which should be set to: 
            // [IGL_COLLAPSE_EDGE_NULL IGL_COLLAPSE_EDGE_NULL IGL_COLLAPSE_EDGE_NULL].
            // Tests whether collapsing exactly two faces and exactly 3 edges from E (e
            // and one side of each face gets collapsed to the other) will result in a
            // mesh with the same topology.
            //
            // Inputs:
            //   e  index into E of edge to try to collapse. E(e,:) = [s d] or [d s] so
            //     that s<d, then d is collapsed to s.
            //   F  #F by 3 list of face indices into V.
            //   E  #E by 2 list of edge indices into V.
            //   EMAP #F*3 list of indices into E, mapping each directed edge to unique
            //     unique edge in E
            //   EF  #E by 2 list of edge flaps, EF(e,0)=f means e=(i-->j) is the edge of
            //     F(f,:) opposite the vth corner, where EI(e,0)=v. Similarly EF(e,1) "
            //     e=(j->i)
            //   EI  #E by 2 list of edge flap corners (see above).
            // Returns true if edge collapse is valid
            IGL_INLINE bool edge_collapse_is_valid(
                const int e,
                const Eigen::MatrixXi& F,
                const Eigen::MatrixXi& E,
                const Eigen::VectorXi& EMAP,
                const Eigen::MatrixXi& EF,
                const Eigen::MatrixXi& EI);

            IGL_INLINE bool edge_collapse_is_valid(
                /*const*/ std::vector<int>& Nsv,
                /*const*/ std::vector<int>& Ndv);

        }

#ifndef IGL_STATIC_LIBRARY
#  include "edge_collapse_is_valid.cpp"
#endif
#endif

    }
    return true;
}

IGL_INLINE bool igl::edge_collapse_is_valid(
    std::vector<int>& Nsv,
    std::vector<int>& Ndv)
{
    // Do we really need to check if edge is IGL_COLLAPSE_EDGE_NULL ?

    if (Nsv.size() < 2 || Ndv.size() < 2)
    {
        // Bogus data
        assert(false);
        return false;
    }
    // determine if the first two vertices are the same before reordering.
    // If they are and there are 3 each, then (I claim) this is an edge on a
    // single tet.
    const bool first_two_same = (Nsv[0] == Ndv[0]) && (Nsv[1] == Ndv[1]);
    if (Nsv.size() == 3 && Ndv.size() == 3 && first_two_same)
    {
        // single tet
        return false;
    }
    // https://stackoverflow.com/a/19483741/148668
    std::sort(Nsv.begin(), Nsv.end());
    std::sort(Ndv.begin(), Ndv.end());
    std::vector<int> Nint;
    std::set_intersection(
        Nsv.begin(), Nsv.end(), Ndv.begin(), Ndv.end(), std::back_inserter(Nint));
    // check if edge collapse is valid: intersection of vertex neighbors of s and
    // d should be exactly 2+(s,d) = 4
    // http://stackoverflow.com/a/27049418/148668
    if (Nint.size() != 2)
    {
        return false;
    }

    return true;
}