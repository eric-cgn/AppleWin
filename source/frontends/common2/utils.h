#pragma once

#include <string>

namespace common2
{
  struct Geometry;

  void setSnapshotFilename(const std::string & filename, const bool load);

  void loadGeometryFromRegistry(const std::string &section, Geometry & geometry);
  void saveGeometryToRegistry(const std::string &section, const Geometry & geometry);
}
