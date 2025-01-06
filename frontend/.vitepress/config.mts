import { defineConfig } from 'vitepress'

// https://vitepress.dev/reference/site-config
export default defineConfig({
  title: "Type Inference Zoo",
  description: "Type Inference Algorithm Collections",
  themeConfig: {
    // https://vitepress.dev/reference/default-theme-config
    nav: [
      { text: 'Home', link: '/' },
      { text: 'Playground', link: '/playground' }
    ],

    sidebar: [],

    socialLinks: [
      { icon: 'github', link: 'https://github.com/cu1ch3n/type-inference-zoo' }
    ]
  }
})
