// This file is part of libigl, a simple c++ geometry processing library.
//
// Copyright (C) 2014 Daniele Panozzo <daniele.panozzo@gmail.com>
//
// This Source Code Form is subject to the terms of the Mozilla Public License
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at http://mozilla.org/MPL/2.0/.

#include "Viewer.h"

//#include <chrono>
#include <thread>

#include <Eigen/LU>


#include <cmath>
#include <cstdio>
#include <sstream>
#include <iomanip>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <limits>
#include <cassert>

#include <igl/project.h>
//#include <igl/get_seconds.h>
#include <igl/readOBJ.h>
#include <igl/readOFF.h>
#include <igl/adjacency_list.h>
#include <igl/writeOBJ.h>
#include <igl/writeOFF.h>
#include <igl/massmatrix.h>
#include <igl/file_dialog_open.h>
#include <igl/file_dialog_save.h>
#include <igl/quat_mult.h>
#include <igl/axis_angle_to_quat.h>
#include <igl/trackball.h>
#include <igl/two_axis_valuator_fixed_up.h>
#include <igl/snap_to_canonical_view_quat.h>
#include <igl/unproject.h>
#include <igl/serialize.h>
#include <igl/shortest_edge_and_midpoint.h>

//New: 
#include <igl/min_heap.h>
#include <igl/edge_flaps.h>
#include <igl/parallel_for.h>
#include <igl/collapse_edge.h>
#include <igl/circulation.h>
#include <igl/decimate.h>
#include <igl/read_triangle_mesh.h>






// Internal global variables used for glfw event handling
//static igl::opengl::glfw::Viewer * __viewer;
static double highdpi = 1;
static double scroll_x = 0;
static double scroll_y = 0;




namespace igl
{
namespace opengl
{
namespace glfw
{
    using namespace std;
    using namespace Eigen;
    using namespace igl;
    


  void Viewer::Init(const std::string config)
  {
     

  }

  //New: 
  //this function create set for each vertex with his faces
  void Viewer::Vertex_to_faces(vector <set <int>>& VF, MatrixXi& F, MatrixXd& V) {
      for (int f = 0; f < F.rows(); f++) 
      {
          for (int v = 0; v < 3; v++)
              VF[F(f, v)].insert(f);
      }
      
  }
  
  // this function create a matrix Q for each vertex v acording to the normals of the vertex faces.
  void Viewer::Create_Q_For_V(Eigen::MatrixXi&F, Eigen::MatrixXd& V, vector <set<int>>& VF, vector<Eigen::Matrix4d> &Q_vertexes) {
      for (int v = 0; v < V.rows(); v++) {
          Q_vertexes[v]=Eigen::Matrix4d::Zero();
      }
      for (int v = 0; v < V.rows(); v++) {
          for (const int& number : VF[v])
          {
              if (F.row(number)(0) == F.row(number)(1) == F.row(number)(2)) {}
              else {
                  VectorXd vec = V.row(v);
                  VectorXd normal = data().F_normals.row(number).normalized();
                  double d = normal(0) * (-vec(0)) + normal(1) * (-vec(1)) + normal(2) * (-vec(2));
                  VectorXd p(4);
                  p(0) = normal(0);
                  p(1) = normal(1);
                  p(2) = normal(2);
                  p(3) = d;
                  Matrix4d temp = p * p.transpose();
                  Q_vertexes[v] = Q_vertexes[v] + temp;
              }
          }
      }
     
  }
 
 
  const auto& calaulate_cost_of_edges = [&](const int e,
      const Eigen::MatrixXd& V,
      const Eigen::MatrixXi& E,
      const std::vector <set<int>>& VF,
      const std::vector<Eigen::Matrix4d>& Q_vertexes,
      const Eigen::MatrixXd& C,
      const igl::min_heap< std::tuple<double, int, int> >& Qmin,
      double& cost,
      Eigen::RowVectorXd& p
      )
  {
        int index_v1 = E.row(e)(0);
        int index_v2 = E.row(e)(1);
        MatrixXd Q1 = Q_vertexes[index_v1];
        MatrixXd Q2 = Q_vertexes[index_v2];
        MatrixXd Q = Q1 + Q2;
        VectorXd new_v(4);
        if (Q.determinant() != 0)
        {
            Q.row(Q.rows() - 1)(0) = 0;
            Q.row(Q.rows() - 1)(1) = 0;
            Q.row(Q.rows() - 1)(2) = 0;
            Q.row(Q.rows() - 1)(3) = 1;
            MatrixXd QInverse = Q.inverse();
            VectorXd v(4);
            v(0) = 0;
            v(1) = 0.0;
            v(2) = 0.0;
            v(3) = 1.0;
            new_v = QInverse * v;
        }
        else 
        {
            VectorXd almost = 0.5 * (V.row(index_v1) + V.row(index_v2));
            new_v(0) = almost(0);
            new_v(1) = almost(1);
            new_v(2) = almost(2);
            new_v(3) = 1;

        }
        RowVectorXd temp = new_v.transpose() * Q;
        cost = (temp * new_v)(0, 0);
        p(0) = new_v(0);
        p(1) = new_v(1);
        p(2) = new_v(2);
  };
  



  //New: from toturial 703
  void Viewer::Reset()
  {
      int i = selected_data_index;
      MatrixXi& F = imagesData.at(i)->F;
      MatrixXd& V = imagesData.at(i)->V;
      VectorXi& EMAP = imagesData.at(i)->EMAP;
      MatrixXi& E = imagesData.at(i)->E;
      MatrixXi& EF = imagesData.at(i)->EF;
      MatrixXi& EI = imagesData.at(i)->EI;
      MatrixXd& C = imagesData.at(i)->C;
      VectorXi& EQ = imagesData.at(i)->EQ;
      int& num_collapsed = imagesData.at(i)->num_collapsed;
      min_heap< std::tuple<double, int, int> >& Q = imagesData.at(i)->Q;
     
      edge_flaps(F, E, EMAP, EF, EI);
      C.resize(E.rows(), V.cols());
      VectorXd costs(E.rows());
      // https://stackoverflow.com/questions/2852140/priority-queue-clear-method
      // Q.clear();
      Q = {};
      EQ = Eigen::VectorXi::Zero(E.rows());
      {
          Eigen::VectorXd costs(E.rows());
          igl::parallel_for(E.rows(), [&](const int e)
              {
                  double cost = e;
                  RowVectorXd p(1, 3);
                  shortest_edge_and_midpoint(e, V, F, E, EMAP, EF, EI, cost, p);
                  C.row(e) = p;
                  costs(e) = cost;
              }, 10000);
          for (int e = 0; e < E.rows(); e++)
          {
              Q.emplace(costs(e), e, 0);
          }
      }
      num_collapsed = 0;
      data().clear();
      data().set_mesh(V, F);
      data().set_face_based(true);
      data().dirty = 157;
      
  }


  //New: from toturial 703
  bool Viewer::Pre_Draw()
  {
     
      int i = selected_data_index;
      MatrixXi& F = imagesData.at(i)->F;
      MatrixXd& V = imagesData.at(i)->V;
      VectorXi& EMAP = imagesData.at(i)->EMAP;
      MatrixXi& E = imagesData.at(i)->E;
      MatrixXi& EF = imagesData.at(i)->EF;
      MatrixXi& EI = imagesData.at(i)->EI;
      MatrixXd& C = imagesData.at(i)->C;
      VectorXi& EQ = imagesData.at(i)->EQ;
      int& num_collapsed = imagesData.at(i)->num_collapsed;
      min_heap< std::tuple<double, int, int> >& Q = imagesData.at(i)->Q;
      
      
      // If animating then collapse 10%/2=5% of edges
      if (!Q.empty())
      {
          bool something_collapsed = false;
          // collapse edge
          const int max_iter = std::ceil(0.01 * Q.size())/2; 
          for (int j = 0; j < max_iter; j++)
          {
              
              if (!collapse_edge(V, F, E, EMAP, EF, EI, Q, EQ, C))
              {
                  break;
              }
              something_collapsed = true;
              num_collapsed++;
          }

          if (something_collapsed)
          {
              data().clear();
              data().set_mesh(V, F);
              data().set_face_based(true);
              data().dirty = 157;
              
              
          }
      }
      return false;
  }



  //------------------------------------------------------New acording to the article----------------------------------------
 
  void Viewer::Reset_2()
  {
      int i = selected_data_index;
      MatrixXi& F = imagesData.at(i)->F;
      MatrixXd& V = imagesData.at(i)->V;
      VectorXi& EMAP = imagesData.at(i)->EMAP;
      MatrixXi& E = imagesData.at(i)->E;
      MatrixXi& EF = imagesData.at(i)->EF;
      MatrixXi& EI = imagesData.at(i)->EI;
      MatrixXd& C = imagesData.at(i)->C;
      VectorXi& EQ = imagesData.at(i)->EQ;
      int& num_collapsed = imagesData.at(i)->num_collapsed;
      min_heap< std::tuple<double, int, int> >& Q = imagesData.at(i)->Q;
      vector <set<int>>& VF = imagesData.at(i)->VF;
      vector <Eigen::Matrix4d>& Q_vertexes = imagesData.at(i)->Q_vertexes;
      VF.resize(V.rows());
      Q_vertexes.resize(V.rows());


      edge_flaps(F, E, EMAP, EF, EI);
      Vertex_to_faces(VF, F, V);
      Create_Q_For_V(F,V, VF, Q_vertexes);
      C.resize(E.rows(), V.cols());
      VectorXd costs(E.rows());
      // https://stackoverflow.com/questions/2852140/priority-queue-clear-method
      // Q.clear();
      Q = {};
      EQ = Eigen::VectorXi::Zero(E.rows());
      {
          Eigen::VectorXd costs(E.rows());
          for (int e = 0; e<E.rows(); e++)
              {
                  double cost = e;
                  RowVectorXd p(1, 3);
                  calaulate_cost_of_edges(e, V, E,VF, Q_vertexes,C, Q, cost, p);
                  C.row(e) = p;
                  costs(e) = cost;
              }
          for (int e = 0; e < E.rows(); e++)
          {
              if (!isnan(costs(e)))
                  Q.emplace(costs(e), e, 0);
              else
                  Q.emplace(INFINITY, e, 0);
              
          }
      }
      num_collapsed = 0;
      data().clear();
      data().set_mesh(V, F);
      data().set_face_based(true);
      data().dirty = 157;

  }

 
  bool Viewer::Pre_Draw_2()
  {

      int i = selected_data_index;
      MatrixXi& F = imagesData.at(i)->F;
      MatrixXd& V = imagesData.at(i)->V;
      VectorXi& EMAP = imagesData.at(i)->EMAP;
      MatrixXi& E = imagesData.at(i)->E;
      MatrixXi& EF = imagesData.at(i)->EF;
      MatrixXi& EI = imagesData.at(i)->EI;
      MatrixXd& C = imagesData.at(i)->C;
      VectorXi& EQ = imagesData.at(i)->EQ;
      int& num_collapsed = imagesData.at(i)->num_collapsed;
      min_heap< std::tuple<double, int, int> >& Q = imagesData.at(i)->Q;
      vector <set<int>>& VF = imagesData.at(i)->VF;
      vector <Eigen::Matrix4d>& Q_vertexes = imagesData.at(i)->Q_vertexes;


      const auto& calaulate_cost_of_edges_2 = [&](const int e,
          const Eigen::MatrixXd& V,
          const Eigen::MatrixXi& E,
          const std::vector <set<int>>& VF,
          const std::vector<Eigen::Matrix4d>& Q_vertexes,
          const Eigen::MatrixXd& C,
          const igl::min_heap< std::tuple<double, int, int> >& Qmin,
          double& cost,
          Eigen::RowVectorXd& p
          )
      {
          int index_v1 = E.row(e)(0);
          int index_v2 = E.row(e)(1);
          MatrixXd Q1 = Q_vertexes[index_v1];
          MatrixXd Q2 = Q_vertexes[index_v2];
          MatrixXd Q = Q1 + Q2;
          VectorXd new_v;
          if (Q.determinant() != 0)
          {
              Q.row(Q.rows() - 1)(0) = 0;
              Q.row(Q.rows() - 1)(1) = 0;
              Q.row(Q.rows() - 1)(2) = 0;
              Q.row(Q.rows() - 1)(3) = 1;
              MatrixXd QInverse = Q.inverse();
              VectorXd v(4);
              v(0) = 0;
              v(1) = 0.0;
              v(2) = 0.0;
              v(3) = 1.0;
              new_v = QInverse * v;
          }
          else
          {
              new_v = 0.5 * (V.row(index_v1) + V.row(index_v2));
          }

          RowVectorXd temp = new_v.transpose() * Q;
          cost = (temp * new_v)(0, 0);
          p(0) = new_v(0);
          p(1) = new_v(1);
          p(2) = new_v(2);


      };






      // If animating then collapse 10%/2=5% of edges
      if (!Q.empty())
      {
          bool something_collapsed = false;
          // collapse edge
          int max_iter = std::ceil(0.01 * Q.size()) /2; 
          if (max_iter == 0)
              max_iter = 1;              
          for (int j = 0; j < max_iter; j++)
          {

              if (!collapse_edge_2(calaulate_cost_of_edges_2, V, F, E, EMAP, EF, EI, Q, EQ, C, VF, Q_vertexes))
              {
                  break;
              }
              something_collapsed = true;
              num_collapsed++;
          }

          if (something_collapsed)
          {
              data().clear();
              data().set_mesh(V, F);
              data().set_face_based(true);
              data().dirty = 157;


          }
      }
      return false;
  }
  
  
  //-----------------------------------------------------New acording to the article-----------------------------------------
  
  



  IGL_INLINE Viewer::Viewer():
    data_list(1),
    selected_data_index(0),
    next_data_id(1),
	isPicked(false),
	isActive(false)
  {
    data_list.front().id = 0;

  

    // Temporary variables initialization
   // down = false;
  //  hack_never_moved = true;
    scroll_position = 0.0f;

    // Per face
    data().set_face_based(false);

    
#ifndef IGL_VIEWER_VIEWER_QUIET
    const std::string usage(R"(igl::opengl::glfw::Viewer usage:
  [drag]  Rotate scene
  A,a     Toggle animation (tight draw loop)
  F,f     Toggle face based
  I,i     Toggle invert normals
  L,l     Toggle wireframe
  O,o     Toggle orthographic/perspective projection
  T,t     Toggle filled faces
  [,]     Toggle between cameras
  1,2     Toggle between models
  ;       Toggle vertex labels
  :       Toggle face labels)"
);
    std::cout<<usage<<std::endl;
#endif
  }

  IGL_INLINE Viewer::~Viewer()
  {
     /* for (int i = 0; i < imagesData.size(); i++) {
          delete imagesData.at(i); //need to the delete the object not inly the pointer
          imagesData.at(i) = nullptr;
      }
      */

  }

  IGL_INLINE bool Viewer::load_mesh_from_file(
      const std::string & mesh_file_name_string)
  {

    // Create new data slot and set to selected
    if(!(data().F.rows() == 0  && data().V.rows() == 0))
    {
      append_mesh();
    }
    data().clear();

    size_t last_dot = mesh_file_name_string.rfind('.');
    if (last_dot == std::string::npos)
    {
      std::cerr<<"Error: No file extension found in "<<
        mesh_file_name_string<<std::endl;
      return false;
    }

    std::string extension = mesh_file_name_string.substr(last_dot+1);

    if (extension == "off" || extension =="OFF")
    {
      Eigen::MatrixXd V;
      Eigen::MatrixXi F;
      if (!igl::readOFF(mesh_file_name_string, V, F))
        return false;
      data().set_mesh(V,F);
    }
    else if (extension == "obj" || extension =="OBJ")
    {
      Eigen::MatrixXd corner_normals;
      Eigen::MatrixXi fNormIndices;

      Eigen::MatrixXd UV_V;
      Eigen::MatrixXi UV_F;
      Eigen::MatrixXd V;
      Eigen::MatrixXi F;

      if (!(
            igl::readOBJ(
              mesh_file_name_string,
              V, UV_V, corner_normals, F, UV_F, fNormIndices)))
      {
        return false;
      }

      data().set_mesh(V,F);
      if (UV_V.rows() > 0)
      {
          data().set_uv(UV_V, UV_F);
      }

    }
    else
    {
      // unrecognized file type
      printf("Error: %s is not a recognized file type.\n",extension.c_str());
      return false;
    }

    data().compute_normals();
    data().uniform_colors(Eigen::Vector3d(51.0/255.0,43.0/255.0,33.3/255.0),
                   Eigen::Vector3d(255.0/255.0,228.0/255.0,58.0/255.0),
                   Eigen::Vector3d(255.0/255.0,235.0/255.0,80.0/255.0));

    // Alec: why?
    if (data().V_uv.rows() == 0)
    {
      data().grid_texture();
    }
    
    //initialize  image data
    ImageData* i = new ImageData();
    i->F = data().F;
    i->V = data().V;
    imagesData.push_back(i);


    //for (unsigned int i = 0; i<plugins.size(); ++i)
    //  if (plugins[i]->post_load())
    //    return true;

    return true;
  }

  IGL_INLINE bool Viewer::save_mesh_to_file(
      const std::string & mesh_file_name_string)
  {
    // first try to load it with a plugin
    //for (unsigned int i = 0; i<plugins.size(); ++i)
    //  if (plugins[i]->save(mesh_file_name_string))
    //    return true;

    size_t last_dot = mesh_file_name_string.rfind('.');
    if (last_dot == std::string::npos)
    {
      // No file type determined
      std::cerr<<"Error: No file extension found in "<<
        mesh_file_name_string<<std::endl;
      return false;
    }
    std::string extension = mesh_file_name_string.substr(last_dot+1);
    if (extension == "off" || extension =="OFF")
    {
      return igl::writeOFF(
        mesh_file_name_string,data().V,data().F);
    }
    else if (extension == "obj" || extension =="OBJ")
    {
      Eigen::MatrixXd corner_normals;
      Eigen::MatrixXi fNormIndices;

      Eigen::MatrixXd UV_V;
      Eigen::MatrixXi UV_F;

      return igl::writeOBJ(mesh_file_name_string,
          data().V,
          data().F,
          corner_normals, fNormIndices, UV_V, UV_F);
    }
    else
    {
      // unrecognized file type
      printf("Error: %s is not a recognized file type.\n",extension.c_str());
      return false;
    }
    return true;
  }
 
  IGL_INLINE bool Viewer::load_scene()
  {
    std::string fname = igl::file_dialog_open();
    if(fname.length() == 0)
      return false;
    return load_scene(fname);
  }

  IGL_INLINE bool Viewer::load_scene(std::string fname)
  {
   // igl::deserialize(core(),"Core",fname.c_str());
    igl::deserialize(data(),"Data",fname.c_str());
    return true;
  }

  IGL_INLINE bool Viewer::save_scene()
  {
    std::string fname = igl::file_dialog_save();
    if (fname.length() == 0)
      return false;
    return save_scene(fname);
  }

  IGL_INLINE bool Viewer::save_scene(std::string fname)
  {
    //igl::serialize(core(),"Core",fname.c_str(),true);
    igl::serialize(data(),"Data",fname.c_str());

    return true;
  }

  IGL_INLINE void Viewer::open_dialog_load_mesh()
  {
    std::string fname = igl::file_dialog_open();

    if (fname.length() == 0)
      return;
    
    this->load_mesh_from_file(fname.c_str());
  }

  IGL_INLINE void Viewer::open_dialog_save_mesh()
  {
    std::string fname = igl::file_dialog_save();

    if(fname.length() == 0)
      return;

    this->save_mesh_to_file(fname.c_str());
  }

  IGL_INLINE ViewerData& Viewer::data(int mesh_id /*= -1*/)
  {
    assert(!data_list.empty() && "data_list should never be empty");
    int index;
    if (mesh_id == -1)
      index = selected_data_index;
    else
      index = mesh_index(mesh_id);

    assert((index >= 0 && index < data_list.size()) &&
      "selected_data_index or mesh_id should be in bounds");
    return data_list[index];
  }

  IGL_INLINE const ViewerData& Viewer::data(int mesh_id /*= -1*/) const
  {
    assert(!data_list.empty() && "data_list should never be empty");
    int index;
    if (mesh_id == -1)
      index = selected_data_index;
    else
      index = mesh_index(mesh_id);

    assert((index >= 0 && index < data_list.size()) &&
      "selected_data_index or mesh_id should be in bounds");
    return data_list[index];
  }

  IGL_INLINE int Viewer::append_mesh(bool visible /*= true*/)
  {
    assert(data_list.size() >= 1);

    data_list.emplace_back();
    selected_data_index = data_list.size()-1;
    data_list.back().id = next_data_id++;
    //if (visible)
    //    for (int i = 0; i < core_list.size(); i++)
    //        data_list.back().set_visible(true, core_list[i].id);
    //else
    //    data_list.back().is_visible = 0;
    return data_list.back().id;
  }

  IGL_INLINE bool Viewer::erase_mesh(const size_t index)
  {
    assert((index >= 0 && index < data_list.size()) && "index should be in bounds");
    assert(data_list.size() >= 1);
    if(data_list.size() == 1)
    {
      // Cannot remove last mesh
      return false;
    }
    data_list[index].meshgl.free();
    data_list.erase(data_list.begin() + index);
    if(selected_data_index >= index && selected_data_index > 0)
    {
      selected_data_index--;
    }

    return true;
  }

  IGL_INLINE size_t Viewer::mesh_index(const int id) const {
    for (size_t i = 0; i < data_list.size(); ++i)
    {
      if (data_list[i].id == id)
        return i;
    }
    return 0;
  }

  Eigen::Matrix4d Viewer::CalcParentsTrans(int indx) 
  {
	  Eigen::Matrix4d prevTrans = Eigen::Matrix4d::Identity();

	  for (int i = indx; parents[i] >= 0; i = parents[i])
	  {
		  //std::cout << "parent matrix:\n" << scn->data_list[scn->parents[i]].MakeTrans() << std::endl;
		  prevTrans = data_list[parents[i]].MakeTransd() * prevTrans;
	  }

	  return prevTrans;
  }

} // end namespace
} // end namespace
}
