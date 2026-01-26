#include "Halide.h"
#include <vector>
#include <string>

int read_args(int argc, char** argv, int& schedule, bool& only_memory, bool& front, bool& non_unique, std::string& name){
    only_memory = false;
    front = false;
    non_unique = false;
    std::string front_s = "front";
    std::string only_memory_s = "mem";
    std::string non_unique_s = "non_unique";
    std::string schedule_s = "schedule";
    
    if(argc == 1){
        printf("Need output name\n");
        return 1;
    }
    name = argv[1];
    bool prev_was_schedule=false;
    schedule = 0;

    for(int i = 2; i < argc; i++){
        if(prev_was_schedule) {
            schedule = std::stoi(argv[i]);
            prev_was_schedule = false;
        } else if(schedule_s.compare(argv[i]) == 0){
            prev_was_schedule = true;
        } else if(front_s.compare(argv[i]) == 0){
            front = true;
        } else if(only_memory_s.compare(argv[i]) == 0){
            only_memory = true;
        } else if(non_unique_s.compare(argv[i]) == 0){
            non_unique = true;
        } else {
            printf("Invallid argument\n");
            return 1;
        }
    }
    if(prev_was_schedule || (front && schedule != 0) || (!front && !(0 <= schedule && schedule <= 3))){
        printf("Invallid argument\n");
        return 1;
    }

    return 0;
}

void set_bounds(std::vector<std::tuple<int, int>> dims, Halide::OutputImageParam p){
    int stride = 1;
    for(int i = 0; i < dims.size(); i++){
        p.dim(i).set_bounds(std::get<0>(dims[i]), std::get<1>(dims[i]));
        p.dim(i).set_stride(stride);
        stride *= std::get<1>(dims[i]);
    }
}

Halide::Target standard_target() {
    Halide::Target target = Halide::Target();
    Halide::Target new_target = target
        .with_feature(Halide::Target::NoAsserts)
        .with_feature(Halide::Target::NoBoundsQuery)
        ;
    return new_target;
}