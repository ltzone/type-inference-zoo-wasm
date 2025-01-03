<template>
  <div class="card flex justify-center">
    <Select v-model="selectedAlg" :options="algs" class="w-full md:w-56" optionLabel="name"
            placeholder="Select an Algorithm"/>
  </div>
</template>

<script setup>
import {ref} from "vue";

const selectedAlg = ref();
const algs = ref([
  {name: 'Algorithm W', code: 'W'},
  {name: 'Elementary', code: 'Elementary'},
]);
</script>
