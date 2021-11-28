// This file is part of libigl, a simple c++ geometry processing library.
// 
// Copyright (C) 2015 Alec Jacobson <alecjacobson@gmail.com>
// 
// This Source Code Form is subject to the terms of the Mozilla Public License 
// v. 2.0. If a copy of the MPL was not distributed with this file, You can 
// obtain one at http://mozilla.org/MPL/2.0/.
#include "collapse_edge.h"
#include "circulation.h"
#include "edge_collapse_is_valid.h"
#include <vector>
//New: 
#include <igl/shortest_edge_and_midpoint.h>
#include <igl\opengl\glfw\Viewer.h>
#include <igl/opengl/glfw/Viewer.h>





IGL_INLINE bool igl::collapse_edge(
  const int e,
  const Eigen::RowVectorXd & p,
  Eigen::MatrixXd & V,
  Eigen::MatrixXi & F,
  Eigen::MatrixXi & E,
  Eigen::VectorXi & EMAP,
  Eigen::MatrixXi & EF,
  Eigen::MatrixXi & EI,
  int & a_e1,
  int & a_e2,
  int & a_f1,
  int & a_f2)
{
  // Assign this to 0 rather than, say, -1 so that deleted elements will get
  // draw as degenerate elements at vertex 0 (which should always exist and
  // never get collapsed to anything else since it is the smallest index)
  using namespace Eigen;
  using namespace std;
  const int eflip = E(e,0)>E(e,1);
  // source and destination
  const int s = eflip?E(e,1):E(e,0);
  const int d = eflip?E(e,0):E(e,1);

  if(!edge_collapse_is_valid(e,F,E,EMAP,EF,EI))
  {
    return false;
  }

  // Important to grab neighbors of d before monkeying with edges
  const std::vector<int> nV2Fd = circulation(e,!eflip,EMAP,EF,EI);

  // The following implementation strongly relies on s<d
  assert(s<d && "s should be less than d");
  // move source and destination to midpoint
  V.row(s) = p;
  V.row(d) = p;

  // Helper function to replace edge and associate information with NULL
  const auto & kill_edge = [&E,&EI,&EF](const int e)
  {
    E(e,0) = IGL_COLLAPSE_EDGE_NULL;
    E(e,1) = IGL_COLLAPSE_EDGE_NULL;
    EF(e,0) = IGL_COLLAPSE_EDGE_NULL;
    EF(e,1) = IGL_COLLAPSE_EDGE_NULL;
    EI(e,0) = IGL_COLLAPSE_EDGE_NULL;
    EI(e,1) = IGL_COLLAPSE_EDGE_NULL;
  };

  // update edge info
  // for each flap
  const int m = F.rows();
  for(int side = 0;side<2;side++)
  {
    const int f = EF(e,side);
    const int v = EI(e,side);
    const int sign = (eflip==0?1:-1)*(1-2*side);
    // next edge emanating from d
    const int e1 = EMAP(f+m*((v+sign*1+3)%3));
    // prev edge pointing to s
    const int e2 = EMAP(f+m*((v+sign*2+3)%3));
    assert(E(e1,0) == d || E(e1,1) == d);
    assert(E(e2,0) == s || E(e2,1) == s);
    // face adjacent to f on e1, also incident on d
    const bool flip1 = EF(e1,1)==f;
    const int f1 = flip1 ? EF(e1,0) : EF(e1,1);
    assert(f1!=f);
    assert(F(f1,0)==d || F(f1,1)==d || F(f1,2) == d);
    // across from which vertex of f1 does e1 appear?
    const int v1 = flip1 ? EI(e1,0) : EI(e1,1);
    // Kill e1
    kill_edge(e1);
    // Kill f
    F(f,0) = IGL_COLLAPSE_EDGE_NULL;
    F(f,1) = IGL_COLLAPSE_EDGE_NULL;
    F(f,2) = IGL_COLLAPSE_EDGE_NULL;
    // map f1's edge on e1 to e2
    assert(EMAP(f1+m*v1) == e1);
    EMAP(f1+m*v1) = e2;
    // side opposite f2, the face adjacent to f on e2, also incident on s
    const int opp2 = (EF(e2,0)==f?0:1);
    assert(EF(e2,opp2) == f);
    EF(e2,opp2) = f1;
    EI(e2,opp2) = v1;
    // remap e2 from d to s
    E(e2,0) = E(e2,0)==d ? s : E(e2,0);
    E(e2,1) = E(e2,1)==d ? s : E(e2,1);
    if(side==0)
    {
      a_e1 = e1;
      a_f1 = f;
    }else
    {
      a_e2 = e1;
      a_f2 = f;
    }
  }

  // finally, reindex faces and edges incident on d. Do this last so asserts
  // make sense.
  //
  // Could actually skip first and last, since those are always the two
  // collpased faces.
  for(auto f : nV2Fd)
  {
    for(int v = 0;v<3;v++)
    {
      if(F(f,v) == d)
      {
        const int flip1 = (EF(EMAP(f+m*((v+1)%3)),0)==f)?1:0;
        const int flip2 = (EF(EMAP(f+m*((v+2)%3)),0)==f)?0:1;
        assert(
          E(EMAP(f+m*((v+1)%3)),flip1) == d ||
          E(EMAP(f+m*((v+1)%3)),flip1) == s);
        E(EMAP(f+m*((v+1)%3)),flip1) = s;
        assert(
          E(EMAP(f+m*((v+2)%3)),flip2) == d ||
          E(EMAP(f+m*((v+2)%3)),flip2) == s);
        E(EMAP(f+m*((v+2)%3)),flip2) = s;
        F(f,v) = s;
        break;
      }
    }
  }
  // Finally, "remove" this edge and its information
  kill_edge(e);

  return true;
}

//New: from toturial 703
IGL_INLINE bool igl::collapse_edge(
    const int e,
    const Eigen::RowVectorXd& p,
    /*const*/ std::vector<int>& Nsv,
    const std::vector<int>& Nsf,
    /*const*/ std::vector<int>& Ndv,
    const std::vector<int>& Ndf,
    Eigen::MatrixXd& V,
    Eigen::MatrixXi& F,
    Eigen::MatrixXi& E,
    Eigen::VectorXi& EMAP,
    Eigen::MatrixXi& EF,
    Eigen::MatrixXi& EI,
    int& a_e1,
    int& a_e2,
    int& a_f1,
    int& a_f2)
{
    // Assign this to 0 rather than, say, -1 so that deleted elements will get
    // draw as degenerate elements at vertex 0 (which should always exist and
    // never get collapsed to anything else since it is the smallest index)
    using namespace Eigen;
    using namespace std;
    const int eflip = E(e, 0) > E(e, 1); // false when e1>e0
    // source and destination
    const int s = eflip ? E(e, 1) : E(e, 0);// small index
    const int d = eflip ? E(e, 0) : E(e, 1);//big index

    if (!edge_collapse_is_valid(Nsv, Ndv))
    {
        return false;
    }

    // OVERLOAD: caller may have just computed this
    //
    // Important to grab neighbors of d before monkeying with edges
    const std::vector<int>& nV2Fd = (!eflip ? Nsf : Ndf);

    // The following implementation strongly relies on s<d
    assert(s < d && "s should be less than d");
    // move source and destination to placement
    V.row(s) = p;
    V.row(d) = p;

    // Helper function to replace edge and associate information with NULL
    const auto& kill_edge = [&E, &EI, &EF](const int e)
    {
        E(e, 0) = IGL_COLLAPSE_EDGE_NULL;
        E(e, 1) = IGL_COLLAPSE_EDGE_NULL;
        EF(e, 0) = IGL_COLLAPSE_EDGE_NULL;
        EF(e, 1) = IGL_COLLAPSE_EDGE_NULL;
        EI(e, 0) = IGL_COLLAPSE_EDGE_NULL;
        EI(e, 1) = IGL_COLLAPSE_EDGE_NULL;
    };

    // update edge info
    // for each flap
    const int m = F.rows();
    for (int side = 0; side < 2; side++)
    {
        const int f = EF(e, side);
        const int v = EI(e, side);
        const int sign = (eflip == 0 ? 1 : -1) * (1 - 2 * side);
        // next edge emanating from d
        const int e1 = EMAP(f + m * ((v + sign * 1 + 3) % 3));
        // prev edge pointing to s
        const int e2 = EMAP(f + m * ((v + sign * 2 + 3) % 3));





        assert(E(e1, 0) == d || E(e1, 1) == d);
        assert(E(e2, 0) == s || E(e2, 1) == s);
        // face adjacent to f on e1, also incident on d
        const bool flip1 = EF(e1, 1) == f;
        const int f1 = flip1 ? EF(e1, 0) : EF(e1, 1);
        assert(f1 != f);
        assert(F(f1, 0) == d || F(f1, 1) == d || F(f1, 2) == d);
        // across from which vertex of f1 does e1 appear?
        const int v1 = flip1 ? EI(e1, 0) : EI(e1, 1);
        // Kill e1
        kill_edge(e1);
        // Kill f
        F(f, 0) = IGL_COLLAPSE_EDGE_NULL;
        F(f, 1) = IGL_COLLAPSE_EDGE_NULL;
        F(f, 2) = IGL_COLLAPSE_EDGE_NULL;
        // map f    1's edge on e1 to e2
        assert(EMAP(f1 + m * v1) == e1);

        EMAP(f1 + m * v1) = e2;
        // side opposite f2, the face adjacent to f on e2, also incident on s
        const int opp2 = (EF(e2, 0) == f ? 0 : 1);
        assert(EF(e2, opp2) == f);
        EF(e2, opp2) = f1;
        EI(e2, opp2) = v1;
        // remap e2 from d to s



        E(e2, 0) = E(e2, 0) == d ? s : E(e2, 0);
        E(e2, 1) = E(e2, 1) == d ? s : E(e2, 1);






        if (side == 0)
        {
            a_e1 = e1;
            a_f1 = f;
        }
        else
        {
            a_e2 = e1;
            a_f2 = f;
        }
    }

    // finally, reindex faces and edges incident on d. Do this last so asserts
    // make sense.
    //
    // Could actually skip first and last, since those are always the two
    // collpased faces. Nah, this is handled by (F(f,v) == d)
    //
    // Don't attempt to use Nde,Nse here because EMAP has changed
    {
        int p1 = -1;
        for (auto f : nV2Fd)
        {
            for (int v = 0; v < 3; v++)
            {
                if (F(f, v) == d)
                {
                    const int e1 = EMAP(f + m * ((v + 1) % 3));
                    const int flip1 = (EF(e1, 0) == f) ? 1 : 0;
                    assert(E(e1, flip1) == d || E(e1, flip1) == s);
                    E(e1, flip1) = s;
                    const int e2 = EMAP(f + m * ((v + 2) % 3));
                    // Skip if we just handled this edge (claim: this will be all except
                    // for the first non-trivial face)
                    if (e2 != p1)
                    {
                        const int flip2 = (EF(e2, 0) == f) ? 0 : 1;
                        assert(E(e2, flip2) == d || E(e2, flip2) == s);
                        E(e2, flip2) = s;
                    }

                    F(f, v) = s;
                    p1 = e1;
                    break;
                }
            }
        }
    }
    // Finally, "remove" this edge and its information
    kill_edge(e);
    return true;
}


IGL_INLINE bool igl::collapse_edge(
  const int e,
  const Eigen::RowVectorXd & p,
  Eigen::MatrixXd & V,
  Eigen::MatrixXi & F,
  Eigen::MatrixXi & E,
  Eigen::VectorXi & EMAP,
  Eigen::MatrixXi & EF,
  Eigen::MatrixXi & EI)
{
  int e1,e2,f1,f2;
  return collapse_edge(e,p,V,F,E,EMAP,EF,EI,e1,e2,f1,f2);
}

IGL_INLINE bool igl::collapse_edge(
  const std::function<void(
    const int,
    const Eigen::MatrixXd &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    const Eigen::VectorXi &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    double &,
    Eigen::RowVectorXd &)> & cost_and_placement,
  Eigen::MatrixXd & V,
  Eigen::MatrixXi & F,
  Eigen::MatrixXi & E,
  Eigen::VectorXi & EMAP,
  Eigen::MatrixXi & EF,
  Eigen::MatrixXi & EI,
  std::set<std::pair<double,int> > & Q,
  std::vector<std::set<std::pair<double,int> >::iterator > & Qit,
  Eigen::MatrixXd & C)
{
  int e,e1,e2,f1,f2;
  const auto always_try = [](
    const Eigen::MatrixXd &                                         ,/*V*/
    const Eigen::MatrixXi &                                         ,/*F*/
    const Eigen::MatrixXi &                                         ,/*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,/*EF*/
    const Eigen::MatrixXi &                                         ,/*EI*/
    const std::set<std::pair<double,int> > &                        ,/*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &,/*Qit*/
    const Eigen::MatrixXd &                                         ,/*C*/
    const int                                                        /*e*/
    ) -> bool { return true;};
  const auto never_care = [](
    const Eigen::MatrixXd &                                         ,   /*V*/
    const Eigen::MatrixXi &                                         ,   /*F*/
    const Eigen::MatrixXi &                                         ,   /*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,  /*EF*/
    const Eigen::MatrixXi &                                         ,  /*EI*/
    const std::set<std::pair<double,int> > &                        ,   /*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &, /*Qit*/
    const Eigen::MatrixXd &                                         ,   /*C*/
    const int                                                       ,   /*e*/
    const int                                                       ,  /*e1*/
    const int                                                       ,  /*e2*/
    const int                                                       ,  /*f1*/
    const int                                                       ,  /*f2*/
    const bool                                                  /*collapsed*/
    )-> void { };
  return 
    collapse_edge(
      cost_and_placement,always_try,never_care,
      V,F,E,EMAP,EF,EI,Q,Qit,C,e,e1,e2,f1,f2);
}

IGL_INLINE bool igl::collapse_edge(
  const std::function<void(
    const int,
    const Eigen::MatrixXd &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    const Eigen::VectorXi &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    double &,
    Eigen::RowVectorXd &)> & cost_and_placement,
  const std::function<bool(
    const Eigen::MatrixXd &                                         ,/*V*/
    const Eigen::MatrixXi &                                         ,/*F*/
    const Eigen::MatrixXi &                                         ,/*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,/*EF*/
    const Eigen::MatrixXi &                                         ,/*EI*/
    const std::set<std::pair<double,int> > &                        ,/*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &,/*Qit*/
    const Eigen::MatrixXd &                                         ,/*C*/
    const int                                                        /*e*/
    )> & pre_collapse,
  const std::function<void(
    const Eigen::MatrixXd &                                         ,   /*V*/
    const Eigen::MatrixXi &                                         ,   /*F*/
    const Eigen::MatrixXi &                                         ,   /*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,  /*EF*/
    const Eigen::MatrixXi &                                         ,  /*EI*/
    const std::set<std::pair<double,int> > &                        ,   /*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &, /*Qit*/
    const Eigen::MatrixXd &                                         ,   /*C*/
    const int                                                       ,   /*e*/
    const int                                                       ,  /*e1*/
    const int                                                       ,  /*e2*/
    const int                                                       ,  /*f1*/
    const int                                                       ,  /*f2*/
    const bool                                                  /*collapsed*/
    )> & post_collapse,
  Eigen::MatrixXd & V,
  Eigen::MatrixXi & F,
  Eigen::MatrixXi & E,
  Eigen::VectorXi & EMAP,
  Eigen::MatrixXi & EF,
  Eigen::MatrixXi & EI,
  std::set<std::pair<double,int> > & Q,
  std::vector<std::set<std::pair<double,int> >::iterator > & Qit,
  Eigen::MatrixXd & C)
{
  int e,e1,e2,f1,f2;
  return 
    collapse_edge(
      cost_and_placement,pre_collapse,post_collapse,
      V,F,E,EMAP,EF,EI,Q,Qit,C,e,e1,e2,f1,f2);
}


IGL_INLINE bool igl::collapse_edge(
  const std::function<void(
    const int,
    const Eigen::MatrixXd &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    const Eigen::VectorXi &,
    const Eigen::MatrixXi &,
    const Eigen::MatrixXi &,
    double &,
    Eigen::RowVectorXd &)> & cost_and_placement,
  const std::function<bool(
    const Eigen::MatrixXd &                                         ,/*V*/
    const Eigen::MatrixXi &                                         ,/*F*/
    const Eigen::MatrixXi &                                         ,/*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,/*EF*/
    const Eigen::MatrixXi &                                         ,/*EI*/
    const std::set<std::pair<double,int> > &                        ,/*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &,/*Qit*/
    const Eigen::MatrixXd &                                         ,/*C*/
    const int                                                        /*e*/
    )> & pre_collapse,
  const std::function<void(
    const Eigen::MatrixXd &                                         ,   /*V*/
    const Eigen::MatrixXi &                                         ,   /*F*/
    const Eigen::MatrixXi &                                         ,   /*E*/
    const Eigen::VectorXi &                                         ,/*EMAP*/
    const Eigen::MatrixXi &                                         ,  /*EF*/
    const Eigen::MatrixXi &                                         ,  /*EI*/
    const std::set<std::pair<double,int> > &                        ,   /*Q*/
    const std::vector<std::set<std::pair<double,int> >::iterator > &, /*Qit*/
    const Eigen::MatrixXd &                                         ,   /*C*/
    const int                                                       ,   /*e*/
    const int                                                       ,  /*e1*/
    const int                                                       ,  /*e2*/
    const int                                                       ,  /*f1*/
    const int                                                       ,  /*f2*/
    const bool                                                  /*collapsed*/
    )> & post_collapse,
  Eigen::MatrixXd & V,
  Eigen::MatrixXi & F,
  Eigen::MatrixXi & E,
  Eigen::VectorXi & EMAP,
  Eigen::MatrixXi & EF,
  Eigen::MatrixXi & EI,
  std::set<std::pair<double,int> > & Q,
  std::vector<std::set<std::pair<double,int> >::iterator > & Qit,
  Eigen::MatrixXd & C,
  int & e,
  int & e1,
  int & e2,
  int & f1,
  int & f2)
{
  using namespace Eigen;
  if(Q.empty())
  {
    // no edges to collapse
    return false;
  }
  std::pair<double,int> p = *(Q.begin());
  if(p.first == std::numeric_limits<double>::infinity())
  {
    // min cost edge is infinite cost
    return false;
  }
  Q.erase(Q.begin());
  e = p.second;
  Qit[e] = Q.end();
  std::vector<int> N  = circulation(e, true,EMAP,EF,EI);
  std::vector<int> Nd = circulation(e,false,EMAP,EF,EI);
  N.insert(N.begin(),Nd.begin(),Nd.end());
  bool collapsed = true;
  if(pre_collapse(V,F,E,EMAP,EF,EI,Q,Qit,C,e))
  {
    collapsed = collapse_edge(e,C.row(e),V,F,E,EMAP,EF,EI,e1,e2,f1,f2);
  }else
  {
    // Aborted by pre collapse callback
    collapsed = false;
  }
  post_collapse(V,F,E,EMAP,EF,EI,Q,Qit,C,e,e1,e2,f1,f2,collapsed);
  if(collapsed)
  {
    // Erase the two, other collapsed edges
    Q.erase(Qit[e1]);
    Qit[e1] = Q.end();
    Q.erase(Qit[e2]);
    Qit[e2] = Q.end();
    // update local neighbors
    // loop over original face neighbors
    for(auto n : N)
    {
      if( F(n,0) != IGL_COLLAPSE_EDGE_NULL ||
          F(n,1) != IGL_COLLAPSE_EDGE_NULL ||
          F(n,2) != IGL_COLLAPSE_EDGE_NULL)
      {
        for(int v = 0;v<3;v++)
        {
          // get edge id
          const int ei = EMAP(v*F.rows()+n);
          // erase old entry
          Q.erase(Qit[ei]);
          // compute cost and potential placement
          double cost ;
          RowVectorXd place;
          cost_and_placement(ei,V,F,E,EMAP,EF,EI,cost,place);
          // Replace in queue
          Qit[ei] = Q.insert(std::pair<double,int>(cost,ei)).first;
          C.row(ei) = place;
        }
      }
    }
  }else
  {
    // reinsert with infinite weight (the provided cost function must **not**
    // have given this un-collapsable edge inf cost already)
    p.first = std::numeric_limits<double>::infinity();
    Qit[e] = Q.insert(p).first;
  }
  return collapsed;
}

//New: from toturial 703
    IGL_INLINE bool igl::collapse_edge(
        Eigen::MatrixXd& V,
        Eigen::MatrixXi& F,
        Eigen::MatrixXi& E,
        Eigen::VectorXi& EMAP,
        Eigen::MatrixXi& EF,
        Eigen::MatrixXi& EI,
        igl::min_heap< std::tuple<double, int, int> >& Q,
        Eigen::VectorXi& EQ,
        Eigen::MatrixXd& C)
    {
        int e, e1, e2, f1, f2;
        return collapse_edge(V, F, E, EMAP, EF, EI, Q, EQ, C, e, e1, e2, f1, f2);
    }

//New: from toturial 703
    IGL_INLINE bool igl::collapse_edge(
        Eigen::MatrixXd& V,
        Eigen::MatrixXi& F,
        Eigen::MatrixXi& E,
        Eigen::VectorXi& EMAP,
        Eigen::MatrixXi& EF,
        Eigen::MatrixXi& EI,
        igl::min_heap< std::tuple<double, int, int> >& Q,
        Eigen::VectorXi& EQ,
        Eigen::MatrixXd& C,
        int& e,
        int& e1,
        int& e2,
        int& f1,
        int& f2)
    {
        using namespace Eigen;
        using namespace igl;
        std::tuple<double, int, int> p;
        while (true)
        {
            // Check if Q is empty
            if (Q.empty())
            {
                // no edges to collapse
                e = -1;
                return false;
            }
            // pop from Q
            p = Q.top();
            // 
            if (std::get<0>(p) == std::numeric_limits<double>::infinity())
            {
                e = -1;
                // min cost edge is infinite cost
                return false;
            }
            Q.pop();
            e = std::get<1>(p);
            // Check if matches timestamp | 
            if (std::get<2>(p) == EQ(e))
            {
                break;
            }
            // must be stale or dead.
            assert(std::get<2>(p) < EQ(e) || EQ(e) == -1);
            // try again.
        }

        // Why is this computed up here?
        // If we just need original face neighbors of edge, could we gather that more
        // directly than gathering face neighbors of each vertex?
        std::vector<int> /*Nse,*/Nsf, Nsv;
        
        circulation(e, true, F, EMAP, EF, EI,/*Nse,*/Nsv, Nsf);
        std::vector<int> /*Nde,*/Ndf, Ndv;
        circulation(e, false, F, EMAP, EF, EI,/*Nde,*/Ndv, Ndf);


        bool collapsed = true;
        collapsed = collapse_edge(
            e, C.row(e),
            Nsv, Nsf, Ndv, Ndf,
            V, F, E, EMAP, EF, EI, e1, e2, f1, f2);



        if (collapsed)
        {
            // Erase the two, other collapsed edges by marking their timestamps as -1
            EQ(e1) = -1;
            EQ(e2) = -1;
            // TODO: visits edges multiple times, ~150% more updates than should
            //
            // update local neighbors
            // loop over original face neighbors
            //
            // Can't use previous computed Nse and Nde because those refer to EMAP
            // before it was changed...
            std::vector<int> Nf;
            Nf.reserve(Nsf.size() + Ndf.size()); // preallocate memory
            Nf.insert(Nf.end(), Nsf.begin(), Nsf.end());
            Nf.insert(Nf.end(), Ndf.begin(), Ndf.end());
            // https://stackoverflow.com/a/1041939/148668
            std::sort(Nf.begin(), Nf.end());
            Nf.erase(std::unique(Nf.begin(), Nf.end()), Nf.end());
            // Collect all edges that must be updated
            std::vector<int> Ne;
            Ne.reserve(3 * Nf.size());
            for (auto& n : Nf)
            {
                if (F(n, 0) != IGL_COLLAPSE_EDGE_NULL ||
                    F(n, 1) != IGL_COLLAPSE_EDGE_NULL ||
                    F(n, 2) != IGL_COLLAPSE_EDGE_NULL)
                {
                    for (int v = 0; v < 3; v++)
                    {
                        // get edge id
                        const int ei = EMAP(v * F.rows() + n);
                        Ne.push_back(ei);
                    }
                }
            }
            // Only process edge once
            std::sort(Ne.begin(), Ne.end());
            Ne.erase(std::unique(Ne.begin(), Ne.end()), Ne.end());
            for (auto& ei : Ne)
            {
                // compute cost and potential placement
                double cost;
                RowVectorXd place;
                shortest_edge_and_midpoint(ei, V, F, E, EMAP, EF, EI, cost, place);
                // Increment timestamp
                EQ(ei)++;
                // Replace in queue
                Q.emplace(cost, ei, EQ(ei));
                C.row(ei) = place;
            }
        }
        else
        {
            // reinsert with infinite weight (the provided cost function must **not**
            // have given this un-collapsable edge inf cost already)
            // Increment timestamp
            EQ(e)++;
            // Replace in queue
            Q.emplace(std::numeric_limits<double>::infinity(), e, EQ(e));
        }
        return collapsed;
    }

  


    //--------------------------------------New Idea for collapse edge acording to the article--------------------------
  
    IGL_INLINE bool igl::collapse_edge_2(
        const std::function<void(
            const int,
            const Eigen::MatrixXd&,
            const Eigen::MatrixXi&,
            const std::vector <std::set<int>>&,
            const std::vector<Eigen::Matrix4d>&,
            const Eigen::MatrixXd&,
            const igl::min_heap< std::tuple<double, int, int> >&,
            double& ,
            Eigen::RowVectorXd& )>& cost_and_placement,
        Eigen::MatrixXd& V,
        Eigen::MatrixXi& F,
        Eigen::MatrixXi& E,
        Eigen::VectorXi& EMAP,
        Eigen::MatrixXi& EF,
        Eigen::MatrixXi& EI,
        igl::min_heap< std::tuple<double, int, int> >& Q,
        Eigen::VectorXi& EQ,
        Eigen::MatrixXd& C,
        std::vector <std::set<int>>& VF,
        std::vector <Eigen::Matrix4d>& Q_vertexes
        ) 
    {
        int e, e1, e2, f1, f2;
        return collapse_edge_2(cost_and_placement, V, F, E, EMAP, EF, EI, Q, EQ, C, VF, Q_vertexes, e, e1, e2, f1, f2);
    }
   
   
    IGL_INLINE bool igl::collapse_edge_2(
        const std::function<void(
            const int,
            const Eigen::MatrixXd&,
            const Eigen::MatrixXi&,
            const std::vector <std::set<int>>&,
            const std::vector<Eigen::Matrix4d>&,
            const Eigen::MatrixXd&,
            const igl::min_heap< std::tuple<double, int, int> >&,
            double& ,
            Eigen::RowVectorXd& )>& cost_and_placement,
        Eigen::MatrixXd& V,
        Eigen::MatrixXi& F,
        Eigen::MatrixXi& E,
        Eigen::VectorXi& EMAP,
        Eigen::MatrixXi& EF,
        Eigen::MatrixXi& EI,
        igl::min_heap< std::tuple<double, int, int> >& Q,
        Eigen::VectorXi& EQ,
        Eigen::MatrixXd& C,
        std::vector <std::set<int>>& VF,
        std::vector <Eigen::Matrix4d>& Q_vertexes,
        int& e,
        int& e1,
        int& e2,
        int& f1,
        int& f2)
    {
        using namespace Eigen;
        using namespace igl;
        std::tuple<double, int, int> p;
        while (true)
        {
            // Check if Q is empty
            if (Q.empty())
            {
                // no edges to collapse
                e = -1;
                return false;
            }
            // pop from Q
            p = Q.top();
            // 
            if (std::get<0>(p) == std::numeric_limits<double>::infinity())
            {
                e = -1;
                // min cost edge is infinite cost
                return false;
            }
            Q.pop();
            e = std::get<1>(p);
            // Check if matches timestamp | 
            if (std::get<2>(p) == EQ(e))
            {
                break;
            }
            // must be stale or dead.
            assert(std::get<2>(p) < EQ(e) || EQ(e) == -1);
            // try again.
        }
        

        // Why is this computed up here?
        // If we just need original face neighbors of edge, could we gather that more
        // directly than gathering face neighbors of each vertex?
        std::vector<int> /*Nse,*/Nsf, Nsv;

        circulation(e, true, F, EMAP, EF, EI,/*Nse,*/Nsv, Nsf);
        std::vector<int> /*Nde,*/Ndf, Ndv;
        circulation(e, false, F, EMAP, EF, EI,/*Nde,*/Ndv, Ndf);


        bool collapsed = true;
        collapsed = collapse_edge(
            e, C.row(e),
            Nsv, Nsf, Ndv, Ndf,
            V, F, E, EMAP, EF, EI, e1, e2, f1, f2);



        if (collapsed)
        {
            // Erase the two, other collapsed edges by marking their timestamps as -1
            EQ(e1) = -1;
            EQ(e2) = -1;
            // TODO: visits edges multiple times, ~150% more updates than should
            //
            // update local neighbors
            // loop over original face neighbors
            //
            // Can't use previous computed Nse and Nde because those refer to EMAP
            // before it was changed...
            std::vector<int> Nf;
            Nf.reserve(Nsf.size() + Ndf.size()); // preallocate memory
            Nf.insert(Nf.end(), Nsf.begin(), Nsf.end());
            Nf.insert(Nf.end(), Ndf.begin(), Ndf.end());
            // https://stackoverflow.com/a/1041939/148668
            std::sort(Nf.begin(), Nf.end());
            Nf.erase(std::unique(Nf.begin(), Nf.end()), Nf.end());
            // Collect all edges that must be updated
            std::vector<int> Ne;
            Ne.reserve(3 * Nf.size());
            for (auto& n : Nf)
            {
                if (F(n, 0) != IGL_COLLAPSE_EDGE_NULL ||
                    F(n, 1) != IGL_COLLAPSE_EDGE_NULL ||
                    F(n, 2) != IGL_COLLAPSE_EDGE_NULL)
                {
                    for (int v = 0; v < 3; v++)
                    {
                        // get edge id
                        const int ei = EMAP(v * F.rows() + n);
                        Ne.push_back(ei);
                    }
                }
            }
            // Only process edge once
            std::sort(Ne.begin(), Ne.end());
            Ne.erase(std::unique(Ne.begin(), Ne.end()), Ne.end());
            for (auto& ei : Ne)
            {
                // compute cost and potential placement
                double cost;
                RowVectorXd place;
                cost_and_placement(ei, V, E, VF, Q_vertexes, C, Q, cost, place);
                // Increment timestamp
                EQ(ei)++;
                // Replace in queue - 
                Q.emplace(cost, ei, EQ(ei)); 
                C.row(ei) = place;
            }
        }
        else
        {
            // reinsert with infinite weight (the provided cost function must **not**
            // have given this un-collapsable edge inf cost already)
            // Increment timestamp
            EQ(e)++;
            // Replace in queue
            Q.emplace(std::numeric_limits<double>::infinity(), e, EQ(e));
        }
        return collapsed;
    }


    
   


