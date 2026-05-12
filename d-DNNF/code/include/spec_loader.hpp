#pragma once

#include <filesystem>

#include "spec_id.hpp"

namespace fo2 {

TypeSystemId load_typesystem_id_from_json(const std::filesystem::path& path, InternTable& interner);

}  // namespace fo2
